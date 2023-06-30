//! This module implements SuperNova NIVC.
// https://eprint.iacr.org/2022/1758.pdf
// By Wyatt Benno 2023.
#![allow(unused_imports)]
#![allow(non_snake_case)]
#![allow(dead_code)]

use crate::ccs;

use crate::{
  constants::{NUM_CHALLENGE_BITS, NUM_FE_FOR_RO},
  errors::NovaError,
  r1cs::{R1CSInstance, R1CSShape, R1CSWitness, RelaxedR1CSInstance, RelaxedR1CSWitness},
  scalar_as_base,
  traits::{
    AbsorbInROTrait, Group, ROConstants, ROConstantsCircuit, ROConstantsTrait, ROTrait,
    circuit::TrivialTestCircuit, circuit::StepCircuit,
    commitment::{CommitmentEngineTrait, CommitmentTrait}},
  Commitment, CommitmentKey, CompressedCommitment,
  PublicParams,
  circuit::{NovaAugmentedCircuit, NovaAugmentedCircuitInputs, NovaAugmentedCircuitParams},
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_FE_WITHOUT_IO_FOR_CRHF, NUM_HASH_BITS}
};

use ff::Field;
use ff::PrimeField;
use core::marker::PhantomData;
use serde::{Deserialize, Serialize};

use crate::bellperson::{
  r1cs::{NovaShape, NovaWitness},
  shape_cs::ShapeCS,
  solver::SatisfyingAssignment,
};
use ::bellperson::{Circuit, ConstraintSystem};


/*
 NIFS (non-interactive folding scheme) is where the folding occurs after the MUX chooses a function.
 It is part of the 'prover'.

 Nova case:
 In a single instance it would take ui, Ui and output Ui+1.
 ui = claim about prior step.
 Ui = running instance.

 SuperNova case:
 In multi-instance it takes:
 - Claim for C'pci_ui
 - pci = the program counter.
 - RC = a array of running instance [Ui-1, Ui-2, ..]

 NIFS returns RESULT = Ui+1,pci.
 A WRITE step takes pci 'aka the current program counter' with RESULT
 and updates RC in the correct index.

 MUX and WRITE functions are needed in the prover.

*/
use crate::nifs::NIFS;

/*
 NIVC contains both prover and verifier.
 It returns an array of updated running claims from NIFS and
 (Zi+1, pci + 1) from the verifier.

 Nova case:
 In a single instance it would additionaly have zi -> C -> zi+1 (the verfier portion of folding)
 z0 = initial input.
 
 SuperNova case:
 In multi-instance it takes as input: 
 - wi = a witness for each step.
 - zi = (witness vector, public input x, the error scalar u)
 - It runs these through two functions Cpci+1 and Phi.

 Cpci+1 outputs Zi+1
 Phi outputs =  pci + 1.

*/


pub struct RunningClaims<G: Group, Ca: StepCircuit<<G as Group>::Scalar>> {
  program_counter: i32,
  RC: Vec<Ca>,
  _phantom: PhantomData<G>, 
}

impl<G: Group, Ca: StepCircuit<<G as Group>::Scalar>> RunningClaims<G, Ca> {
  pub fn new() -> Self {
      Self {
          program_counter: 0,
          RC: Vec::new(),
          _phantom: PhantomData, 
      }
  }

  pub fn push_circuit(&mut self, circuit: Ca) {
    self.RC.push(circuit);
  }
}

/// A SNARK that proves the correct execution of an incremental computation
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct NivcSNARK<G1, G2, C1, C2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
{
  r_W_primary: RelaxedR1CSWitness<G1>,
  r_U_primary: RelaxedR1CSInstance<G1>,
  r_W_secondary: RelaxedR1CSWitness<G2>,
  r_U_secondary: RelaxedR1CSInstance<G2>,
  l_w_secondary: R1CSWitness<G2>,
  l_u_secondary: R1CSInstance<G2>,
  i: usize,
  zi_primary: Vec<G1::Scalar>,
  zi_secondary: Vec<G2::Scalar>,
  _p_c1: PhantomData<C1>,
  _p_c2: PhantomData<C2>,
}

impl<G1, G2, C1, C2> NivcSNARK<G1, G2, C1, C2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
{
  /// Create a new `NivcSNARK` (or updates the provided `NivcSNARK`)
  /// by executing a step of the incremental computation
  pub fn prove_step(
    pp: &PublicParams<G1, G2, C1, C2>,
    recursive_snark: Option<Self>,
    c_primary: C1,
    c_secondary: C2,
    z0_primary: Vec<G1::Scalar>,
    z0_secondary: Vec<G2::Scalar>,
  ) -> Result<Self, NovaError> {
    if z0_primary.len() != pp.F_arity_primary || z0_secondary.len() != pp.F_arity_secondary {
      return Err(NovaError::InvalidInitialInputLength);
    }

    match recursive_snark {
      None => {
        // base case for the primary
        let mut cs_primary: SatisfyingAssignment<G1> = SatisfyingAssignment::new();
        let inputs_primary: NovaAugmentedCircuitInputs<G2> = NovaAugmentedCircuitInputs::new(
          scalar_as_base::<G1>(pp.digest),
          G1::Scalar::ZERO,
          z0_primary.clone(),
          None,
          None,
          None,
          None,
        );

        let circuit_primary: NovaAugmentedCircuit<G2, C1> = NovaAugmentedCircuit::new(
          pp.augmented_circuit_params_primary.clone(),
          Some(inputs_primary),
          c_primary.clone(),
          pp.ro_consts_circuit_primary.clone(),
        );
        let _ = circuit_primary.synthesize(&mut cs_primary);
        let (u_primary, w_primary) = cs_primary
          .r1cs_instance_and_witness(&pp.r1cs_shape_primary, &pp.ck_primary)
          .map_err(|_e| NovaError::UnSat)?;

        // base case for the secondary
        let mut cs_secondary: SatisfyingAssignment<G2> = SatisfyingAssignment::new();
        let inputs_secondary: NovaAugmentedCircuitInputs<G1> = NovaAugmentedCircuitInputs::new(
          pp.digest,
          G2::Scalar::ZERO,
          z0_secondary.clone(),
          None,
          None,
          Some(u_primary.clone()),
          None,
        );
        let circuit_secondary: NovaAugmentedCircuit<G1, C2> = NovaAugmentedCircuit::new(
          pp.augmented_circuit_params_secondary.clone(),
          Some(inputs_secondary),
          c_secondary.clone(),
          pp.ro_consts_circuit_secondary.clone(),
        );
        let _ = circuit_secondary.synthesize(&mut cs_secondary);
        let (u_secondary, w_secondary) = cs_secondary
          .r1cs_instance_and_witness(&pp.r1cs_shape_secondary, &pp.ck_secondary)
          .map_err(|_e| NovaError::UnSat)?;

        // IVC proof for the primary circuit
        let l_w_primary = w_primary;
        let l_u_primary = u_primary;
        let r_W_primary =
          RelaxedR1CSWitness::from_r1cs_witness(&pp.r1cs_shape_primary, &l_w_primary);
        let r_U_primary = RelaxedR1CSInstance::from_r1cs_instance(
          &pp.ck_primary,
          &pp.r1cs_shape_primary,
          &l_u_primary,
        );

        // IVC proof of the secondary circuit
        let l_w_secondary = w_secondary;
        let l_u_secondary = u_secondary;
        let r_W_secondary = RelaxedR1CSWitness::<G2>::default(&pp.r1cs_shape_secondary);
        let r_U_secondary =
          RelaxedR1CSInstance::<G2>::default(&pp.ck_secondary, &pp.r1cs_shape_secondary);

        // Outputs of the two circuits thus far
        let zi_primary = c_primary.output(&z0_primary);
        let zi_secondary = c_secondary.output(&z0_secondary);

        if zi_primary.len() != pp.F_arity_primary || zi_secondary.len() != pp.F_arity_secondary {
          return Err(NovaError::InvalidStepOutputLength);
        }

        Ok(Self {
          r_W_primary,
          r_U_primary,
          r_W_secondary,
          r_U_secondary,
          l_w_secondary,
          l_u_secondary,
          i: 1_usize,
          zi_primary,
          zi_secondary,
          _p_c1: Default::default(),
          _p_c2: Default::default(),
        })
      }
      Some(r_snark) => {
        // fold the secondary circuit's instance
        let (nifs_secondary, (r_U_secondary, r_W_secondary)) = NIFS::prove(
          &pp.ck_secondary,
          &pp.ro_consts_secondary,
          &scalar_as_base::<G1>(pp.digest),
          &pp.r1cs_shape_secondary,
          &r_snark.r_U_secondary,
          &r_snark.r_W_secondary,
          &r_snark.l_u_secondary,
          &r_snark.l_w_secondary,
        )?;

        let mut cs_primary: SatisfyingAssignment<G1> = SatisfyingAssignment::new();
        let inputs_primary: NovaAugmentedCircuitInputs<G2> = NovaAugmentedCircuitInputs::new(
          scalar_as_base::<G1>(pp.digest),
          G1::Scalar::from(r_snark.i as u64),
          z0_primary,
          Some(r_snark.zi_primary.clone()),
          Some(r_snark.r_U_secondary.clone()),
          Some(r_snark.l_u_secondary.clone()),
          Some(Commitment::<G2>::decompress(&nifs_secondary.comm_T)?),
        );

        let circuit_primary: NovaAugmentedCircuit<G2, C1> = NovaAugmentedCircuit::new(
          pp.augmented_circuit_params_primary.clone(),
          Some(inputs_primary),
          c_primary.clone(),
          pp.ro_consts_circuit_primary.clone(),
        );
        let _ = circuit_primary.synthesize(&mut cs_primary);

        let (l_u_primary, l_w_primary) = cs_primary
          .r1cs_instance_and_witness(&pp.r1cs_shape_primary, &pp.ck_primary)
          .map_err(|_e| NovaError::UnSat)?;

        // fold the primary circuit's instance
        let (nifs_primary, (r_U_primary, r_W_primary)) = NIFS::prove(
          &pp.ck_primary,
          &pp.ro_consts_primary,
          &pp.digest,
          &pp.r1cs_shape_primary,
          &r_snark.r_U_primary,
          &r_snark.r_W_primary,
          &l_u_primary,
          &l_w_primary,
        )?;

        let mut cs_secondary: SatisfyingAssignment<G2> = SatisfyingAssignment::new();
        let inputs_secondary: NovaAugmentedCircuitInputs<G1> = NovaAugmentedCircuitInputs::new(
          pp.digest,
          G2::Scalar::from(r_snark.i as u64),
          z0_secondary,
          Some(r_snark.zi_secondary.clone()),
          Some(r_snark.r_U_primary.clone()),
          Some(l_u_primary),
          Some(Commitment::<G1>::decompress(&nifs_primary.comm_T)?),
        );

        let circuit_secondary: NovaAugmentedCircuit<G1, C2> = NovaAugmentedCircuit::new(
          pp.augmented_circuit_params_secondary.clone(),
          Some(inputs_secondary),
          c_secondary.clone(),
          pp.ro_consts_circuit_secondary.clone(),
        );
        let _ = circuit_secondary.synthesize(&mut cs_secondary);

        let (l_u_secondary, l_w_secondary) = cs_secondary
          .r1cs_instance_and_witness(&pp.r1cs_shape_secondary, &pp.ck_secondary)
          .map_err(|_e| NovaError::UnSat)?;

        // update the running instances and witnesses
        let zi_primary = c_primary.output(&r_snark.zi_primary);
        let zi_secondary = c_secondary.output(&r_snark.zi_secondary);

        Ok(Self {
          r_W_primary,
          r_U_primary,
          r_W_secondary,
          r_U_secondary,
          l_w_secondary,
          l_u_secondary,
          i: r_snark.i + 1,
          zi_primary,
          zi_secondary,
          _p_c1: Default::default(),
          _p_c2: Default::default(),
        })
      }
    }
  }

  /// Verify the correctness of the `NivcSNARK`
  pub fn verify(
    &self,
    pp: &PublicParams<G1, G2, C1, C2>,
    num_steps: usize,
    z0_primary: Vec<G1::Scalar>,
    z0_secondary: Vec<G2::Scalar>,
  ) -> Result<(Vec<G1::Scalar>, Vec<G2::Scalar>), NovaError> {
    // number of steps cannot be zero
    if num_steps == 0 {
      return Err(NovaError::ProofVerifyError);
    }

    // check if the provided proof has executed num_steps
    if self.i != num_steps {
      return Err(NovaError::ProofVerifyError);
    }

    // check if the (relaxed) R1CS instances have two public outputs
    if self.l_u_secondary.X.len() != 2
      || self.r_U_primary.X.len() != 2
      || self.r_U_secondary.X.len() != 2
    {
      return Err(NovaError::ProofVerifyError);
    }

    // check if the output hashes in R1CS instances point to the right running instances
    let (hash_primary, hash_secondary) = {
      let mut hasher = <G2 as Group>::RO::new(
        pp.ro_consts_secondary.clone(),
        NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * pp.F_arity_primary,
      );
      hasher.absorb(pp.digest);
      hasher.absorb(G1::Scalar::from(num_steps as u64));
      for e in &z0_primary {
        hasher.absorb(*e);
      }
      for e in &self.zi_primary {
        hasher.absorb(*e);
      }
      self.r_U_secondary.absorb_in_ro(&mut hasher);

      let mut hasher2 = <G1 as Group>::RO::new(
        pp.ro_consts_primary.clone(),
        NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * pp.F_arity_secondary,
      );
      hasher2.absorb(scalar_as_base::<G1>(pp.digest));
      hasher2.absorb(G2::Scalar::from(num_steps as u64));
      for e in &z0_secondary {
        hasher2.absorb(*e);
      }
      for e in &self.zi_secondary {
        hasher2.absorb(*e);
      }
      self.r_U_primary.absorb_in_ro(&mut hasher2);

      (
        hasher.squeeze(NUM_HASH_BITS),
        hasher2.squeeze(NUM_HASH_BITS),
      )
    };

    if hash_primary != self.l_u_secondary.X[0]
      || hash_secondary != scalar_as_base::<G2>(self.l_u_secondary.X[1])
    {
      return Err(NovaError::ProofVerifyError);
    }

    // check the satisfiability of the provided instances
    let (res_r_primary, (res_r_secondary, res_l_secondary)) = rayon::join(
      || {
        pp.r1cs_shape_primary
          .is_sat_relaxed(&pp.ck_primary, &self.r_U_primary, &self.r_W_primary)
      },
      || {
        rayon::join(
          || {
            pp.r1cs_shape_secondary.is_sat_relaxed(
              &pp.ck_secondary,
              &self.r_U_secondary,
              &self.r_W_secondary,
            )
          },
          || {
            pp.r1cs_shape_secondary.is_sat(
              &pp.ck_secondary,
              &self.l_u_secondary,
              &self.l_w_secondary,
            )
          },
        )
      },
    );

    // check the returned res objects
    res_r_primary?;
    res_r_secondary?;
    res_l_secondary?;

    Ok((self.zi_primary.clone(), self.zi_secondary.clone()))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use ::bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};

  #[derive(Clone, Debug, Default)]
  struct CubicCircuit<F: PrimeField> {
    _p: PhantomData<F>,
  }

  impl<F> StepCircuit<F> for CubicCircuit<F>
  where
    F: PrimeField,
  {
    fn arity(&self) -> usize {
      1
    }

    fn synthesize<CS: ConstraintSystem<F>>(
      &self,
      cs: &mut CS,
      z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
      // Consider a cubic equation: `x^3 + x + 5 = y`, where `x` and `y` are respectively the input and output.
      let x = &z[0];
      let x_sq = x.square(cs.namespace(|| "x_sq"))?;
      let x_cu = x_sq.mul(cs.namespace(|| "x_cu"), x)?;
      let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
        Ok(x_cu.get_value().unwrap() + x.get_value().unwrap() + F::from(5u64))
      })?;

      cs.enforce(
        || "y = x^3 + x + 5",
        |lc| {
          lc + x_cu.get_variable()
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

      Ok(vec![y])
    }

    fn output(&self, z: &[F]) -> Vec<F> {
      vec![z[0] * z[0] * z[0] + z[0] + F::from(5u64)]
    }
  }


  type G1 = pasta_curves::pallas::Point;
  type G2 = pasta_curves::vesta::Point;

  fn test_trivial_nivc_with<G1, G2, T: StepCircuit<<G1 as Group>::Scalar>>(pci: i32, t1: &T)
  where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
    T: StepCircuit<<G1 as Group>::Scalar> + std::fmt::Debug,
  {
    let default_circuit = TrivialTestCircuit::<<G2 as Group>::Scalar>::default();

    println!("here: {:?}", t1);

    // produce public parameters
    let pp = PublicParams::<
      G1,
      G2,
      T,
      TrivialTestCircuit<<G2 as Group>::Scalar>,
    >::setup(t1.clone(), default_circuit.clone());

    let num_steps = 1;

    // produce a recursive SNARK
    let mut recursive_snark: Option<
    NivcSNARK<
      G1,
      G2,
      T,
      TrivialTestCircuit<<G2 as Group>::Scalar>,
    >,
  > = None;

    // produce a recursive SNARK
    let res = NivcSNARK::prove_step(
      &pp,
      recursive_snark,
      t1.clone(),
      default_circuit,
      vec![<G1 as Group>::Scalar::ZERO],
      vec![<G2 as Group>::Scalar::ZERO],
    );
    assert!(res.is_ok());
    let recursive_snark_unwrapped = res.unwrap();

    // verify the recursive SNARK
    let res = recursive_snark_unwrapped.verify(
      &pp,
      num_steps,
      vec![<G1 as Group>::Scalar::ZERO],
      vec![<G2 as Group>::Scalar::ZERO],
    );
    assert!(res.is_ok());
  }

  #[test]
  fn test_trivial_nivc() {
      // Structuring running claims      
      let mut running_claim1 = RunningClaims::<G1, CubicCircuit<<G1 as Group>::Scalar>>::new();
      let test_circuit1 = CubicCircuit::<<G1 as Group>::Scalar>::default();
      running_claim1.push_circuit(test_circuit1);

      let mut running_claim2 = RunningClaims::<G1, CubicCircuit<<G1 as Group>::Scalar>>::new();
      let test_circuit2 = CubicCircuit::<<G1 as Group>::Scalar>::default();
      running_claim2.push_circuit(test_circuit2);

      let claims_tuple = (running_claim1, running_claim2);
    
      //Expirementing with selecting the running claims for nifs
      test_trivial_nivc_with::<G1, G2, CubicCircuit<<G1 as Group>::Scalar>>(
        claims_tuple.0.program_counter,
        &claims_tuple.0.RC[0],
      );

      /*test_trivial_nivc_with::<G1, G2, CubicCircuit<<G1 as Group>::Scalar>>(
        claims_tuple.1.program_counter,
        &claims_tuple.1.RC[0],
        &claims_tuple.1.RC[0]
      );*/

  }
}

