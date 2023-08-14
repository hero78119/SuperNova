use crate::gadgets::utils::alloc_const;
use crate::gadgets::utils::alloc_num_equals;
use crate::gadgets::utils::conditionally_select;
use crate::traits::circuit_supernova::StepCircuit;
use crate::traits::Group;
use crate::{
  compute_digest,
  gadgets::utils::{add_allocated_num, alloc_one, alloc_zero},
};
use bellperson::gadgets::boolean::Boolean;
use bellperson::LinearCombination;
use core::marker::PhantomData;
use ff::Field;
use ff::PrimeField;
use log::info;

use crate::supernova::*;

use ::bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};

fn init() {
  let _ = env_logger::builder().is_test(true).try_init();
}

fn constraint_augmented_circuit_index<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  pc_counter: &AllocatedNum<F>,
  rom: &[AllocatedNum<F>],
  circuit_index: &AllocatedNum<F>,
) -> Result<(), SynthesisError> {
  // select target when index match or empty
  let zero = alloc_zero(cs.namespace(|| "zero"))?;
  let rom_values = rom
    .iter()
    .enumerate()
    .map(|(i, rom_value)| {
      let index_alloc = alloc_const(
        cs.namespace(|| format!("rom_values {} index ", i)),
        F::from(i as u64),
      )?;
      let equal_bit = Boolean::from(alloc_num_equals(
        cs.namespace(|| format!("rom_values {} equal bit", i)),
        &index_alloc,
        pc_counter,
      )?);
      conditionally_select(
        cs.namespace(|| format!("rom_values {} conditionally_select ", i)),
        rom_value,
        &zero,
        &equal_bit,
      )
    })
    .collect::<Result<Vec<AllocatedNum<F>>, SynthesisError>>()?;

  let sum_lc = rom_values
    .iter()
    .fold(LinearCombination::<F>::zero(), |acc_lc, row_value| {
      acc_lc + row_value.get_variable()
    });

  cs.enforce(
    || "sum_lc == circuit_index",
    |lc| lc + circuit_index.get_variable() - &sum_lc,
    |lc| lc + CS::one(),
    |lc| lc,
  );

  Ok(())
}

#[derive(Clone, Debug, Default)]
struct PrimaryCircuit<F: PrimeField> {
  _p: PhantomData<F>,
  circuit_index: usize,
  rom_size: usize,
}

impl<F> PrimaryCircuit<F>
where
  F: PrimeField,
{
  fn new(circuit_index: usize, rom_size: usize) -> Self {
    PrimaryCircuit {
      circuit_index,
      rom_size,
      _p: PhantomData,
    }
  }
}

impl<F> StepCircuit<F> for PrimaryCircuit<F>
where
  F: PrimeField,
{
  fn arity(&self) -> usize {
    1 + self.rom_size // value + rom[].len()
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    pc_counter: &AllocatedNum<F>,
    z: &[AllocatedNum<F>],
  ) -> Result<(AllocatedNum<F>, Vec<AllocatedNum<F>>), SynthesisError> {
    // constrain rom[pc] equal to `self.circuit_index`
    let circuit_index = alloc_const(
      cs.namespace(|| "circuit_index"),
      F::from(self.circuit_index as u64),
    )?;
    constraint_augmented_circuit_index(
      cs.namespace(|| "SquareCircuit agumented circuit constraint"),
      pc_counter,
      &z[1..],
      &circuit_index,
    )?;
    let one = alloc_one(cs.namespace(|| "alloc one"))?;
    let pc_next = add_allocated_num(
      // pc = pc + 1
      cs.namespace(|| "pc = pc + 1"),
      pc_counter,
      &one,
    )?;

    // Consider an equation: `x^2 + x + 5 = y`, where `x` and `y` are respectively the input and output.
    let x = &z[0];
    let x_sq = x.square(cs.namespace(|| "x_sq"))?;
    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
      Ok(x_sq.get_value().unwrap() + x.get_value().unwrap() + F::from(5u64))
    })?;

    cs.enforce(
      || "y = x^2 + x + 5",
      |lc| {
        lc + x_sq.get_variable()
          + x.get_variable()
          + CS::one()
          + CS::one()
          + CS::one()
          + CS::one()
          + CS::one()
      },
      |lc| lc + CS::one(),
      |lc| lc + y.get_variable(),
    );

    let mut z_next = vec![y];
    z_next.extend(z[1..].iter().cloned());
    Ok((pc_next, z_next))
  }
}

#[derive(Clone, Debug, Default)]
struct SecondaryCircuit<F: PrimeField> {
  num_cons: usize,
  rom_size: usize,
  _p: PhantomData<F>,
}

impl<F> SecondaryCircuit<F>
where
  F: PrimeField,
{
  pub fn new(num_cons: usize, rom_size: usize) -> Self {
    Self {
      num_cons,
      rom_size,
      _p: Default::default(),
    }
  }
}
impl<F> StepCircuit<F> for SecondaryCircuit<F>
where
  F: PrimeField,
{
  fn arity(&self) -> usize {
    1 + self.rom_size
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    pc: &AllocatedNum<F>,
    z: &[AllocatedNum<F>],
  ) -> Result<(AllocatedNum<F>, Vec<AllocatedNum<F>>), SynthesisError> {
    for i in 0..self.num_cons {
      _ = z[0].clone().square(cs.namespace(|| format!("x_sq_{i}")))?;
    }
    Ok((pc.clone(), z.to_vec()))
  }
}

const OPCODE_0: usize = 0;
const OPCODE_1: usize = 1;
fn test_trivial_nivc_with<G1, G2>(
  rom: &[usize],
  num_primary_augmented_circuit: usize,
  shared_secondary_circuit: bool,
) where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  // This test also ready to add more argumented circuit and ROM can be arbitrary length

  // ROM is for constraints the sequence of execution order for opcode
  // program counter initially point to 0

  // TODO: replace with memory commitment along with suggestion from Supernova 4.4 optimisations

  // This is mostly done with the existing Nova code. With additions of U_i[] and program_counter checks
  // in the augmented circuit.

  // To save the test time, after each step of iteration, RecursiveSNARK just verfiy the latest U_i[augmented_circuit_index] needs to be a satisfying instance.
  // TODO At the end of this test, RecursiveSNARK need to verify all U_i[] are satisfying instances

  let (num_secondary_augmented_circuit, circuits_secondary) = if shared_secondary_circuit {
    (
      1,
      vec![(0, SecondaryCircuit::new(0, rom.len())); num_primary_augmented_circuit],
    )
  } else {
    (
      num_primary_augmented_circuit,
      (0..num_primary_augmented_circuit)
        .map(|i| (i, SecondaryCircuit::new(i, rom.len())))
        .collect::<Vec<(usize, SecondaryCircuit<<G2 as Group>::Scalar>)>>(),
    )
  };

  let mut running_claims = (0..num_primary_augmented_circuit)
    .zip(circuits_secondary.iter())
    .map(
      |(i, (secondary_augmented_circuit_index, circuit_seconday))| {
        let test_circuit = PrimaryCircuit::new(i, rom.len());
        RunningClaim::<
          G1,
          G2,
          PrimaryCircuit<<G1 as Group>::Scalar>,
          SecondaryCircuit<<G2 as Group>::Scalar>,
        >::new(
          i,
          *secondary_augmented_circuit_index,
          test_circuit,
          circuit_seconday.clone(),
          num_primary_augmented_circuit,
          num_secondary_augmented_circuit,
        )
      },
    )
    .collect::<Vec<
      RunningClaim<
        G1,
        G2,
        PrimaryCircuit<<G1 as Group>::Scalar>,
        SecondaryCircuit<<G2 as Group>::Scalar>,
      >,
    >>();

  // generate the commitkey based on max num of constraints and reused it for all other augmented circuit
  let (max_primary_circuit_index, _) = running_claims
    .iter()
    .enumerate()
    .map(|(i, claim)| -> (usize, usize) { (i, claim.params.r1cs_shape_primary.num_cons) })
    .max_by(|(_, circuit_size1), (_, circuit_size2)| circuit_size1.cmp(circuit_size2))
    .unwrap();

  let (r1cs_shape_primary, _) = running_claims[max_primary_circuit_index].get_r1cs_shape();
  // max_secondary_circuit appear on the last one
  let (_, r1cs_shape_secondary) = running_claims[running_claims.len() - 1].get_r1cs_shape();

  let ck_primary = gen_commitmentkey_by_r1cs(r1cs_shape_primary);
  let ck_secondary = gen_commitmentkey_by_r1cs(r1cs_shape_secondary);

  // set unified ck_primary, ck_secondary and update digest

  running_claims
    .iter_mut()
    .for_each(|claim| claim.set_commitmentkey(ck_primary.clone(), ck_secondary.clone()));

  let digest = compute_digest::<G1, PublicParams<G1, G2>>(
    &running_claims
      .iter()
      .map(|claim| claim.get_publicparams())
      .collect::<Vec<&PublicParams<G1, G2>>>()[..],
  );

  let num_steps = rom.len();
  let initial_program_counter = <G1 as Group>::Scalar::from(0);

  // extend z0_primary/secondary with rom content
  let mut z0_primary = vec![<G1 as Group>::Scalar::ONE];
  z0_primary.extend(
    rom
      .iter()
      .map(|opcode| <G1 as Group>::Scalar::from(*opcode as u64)),
  );
  let mut z0_secondary = vec![<G2 as Group>::Scalar::ONE];
  z0_secondary.extend(
    rom
      .iter()
      .map(|opcode| <G2 as Group>::Scalar::from(*opcode as u64)),
  );

  let mut recursive_snark_option: Option<RecursiveSNARK<G1, G2>> = None;

  for _ in 0..num_steps {
    let program_counter = recursive_snark_option
      .as_ref()
      .map(|recursive_snark| recursive_snark.program_counter)
      .unwrap_or_else(|| initial_program_counter);
    let augmented_circuit_index = rom[u32::from_le_bytes(
      // convert program counter from field to usize (only took le 4 bytes)
      program_counter.to_repr().as_ref()[0..4].try_into().unwrap(),
    ) as usize];

    let running_claim = running_claims
      .get(augmented_circuit_index)
      .unwrap_or_else(|| unimplemented!("unimplemented opcode index {}", augmented_circuit_index));
    let mut recursive_snark = recursive_snark_option.unwrap_or_else(|| {
      RecursiveSNARK::iter_base_step(
        &running_claim,
        digest,
        program_counter,
        num_primary_augmented_circuit,
        num_secondary_augmented_circuit,
        &z0_primary,
        &z0_secondary,
      )
      .map_err(|err| debug!("err {:?}", err))
      .unwrap()
    });

    let _ = recursive_snark
      .prove_step(running_claim, &z0_primary, &z0_secondary)
      .map_err(|err| debug!("err {:?}", err))
      .unwrap();
    let _ = recursive_snark
      .verify(running_claim, &z0_primary, &z0_secondary)
      .map_err(|err| debug!("err {:?}", err))
      .unwrap();
    recursive_snark_option = Some(recursive_snark)
  }

  assert!(recursive_snark_option.is_some());

  // Now you can handle the Result using if let
  let RecursiveSNARK {
    zi_primary,
    zi_secondary,
    program_counter,
    ..
  } = &recursive_snark_option.unwrap();

  info!("zi_primary: {:?}", zi_primary);
  info!("zi_secondary: {:?}", zi_secondary);
  info!("final program_counter: {:?}", program_counter);
}

#[test]
fn test_trivial_nivc() {
  init();
  type G1 = pasta_curves::pallas::Point;
  type G2 = pasta_curves::vesta::Point;

  // Here demo a simple RAM machine
  // - with 2 argumented circuit
  // - each argumented circuit contains primary and secondary circuit
  // - a memory commmitment via a public IO `rom` (like a program) to constraint the sequence execution

  let rom = [
    OPCODE_1, OPCODE_1, OPCODE_0, OPCODE_0, OPCODE_1, OPCODE_1, OPCODE_0, OPCODE_0, OPCODE_1,
    OPCODE_1,
  ]; // Rom can be arbitrary length.

  test_trivial_nivc_with::<G1, G2>(&rom, 2, true);
  // test_trivial_nivc_with::<G1, G2>(&rom, 2, false);
}
