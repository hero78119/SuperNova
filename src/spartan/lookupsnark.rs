//! This module implements LookupSNARK which leverage memory-offline-check skills
use crate::{
  constants::NUM_CHALLENGE_BITS,
  digest::{DigestComputer, SimpleDigestible},
  errors::NovaError,
  gadgets::{lookup::Lookup, utils::scalar_as_base},
  spartan::{
    math::Math,
    polys::{
      eq::EqPolynomial,
      identity::IdentityPolynomial,
      multilinear::MultilinearPolynomial,
      univariate::{CompressedUniPoly, UniPoly},
    },
    powers,
    sumcheck::SumcheckProof,
    PolyEvalInstance, PolyEvalWitness,
  },
  traits::{
    commitment::{CommitmentEngineTrait, CommitmentTrait},
    evaluation::EvaluationEngineTrait,
    AbsorbInROTrait, ROTrait, TranscriptEngineTrait,
  },
  Commitment, CommitmentKey, CompressedCommitment,
};
use abomonation::Abomonation;
use abomonation_derive::Abomonation;
use core::marker::PhantomData;
use ff::{Field, PrimeField};

use crate::spartan::ppsnark::vec_to_arr;
use crate::Engine;
use once_cell::sync::OnceCell;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

/// A type that represents the prover's key
#[derive(Clone, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_bounds(where <E::Scalar as PrimeField>::Repr: Abomonation)]
pub struct ProverKey<E: Engine, EE: EvaluationEngineTrait<E>> {
  pk_ee: EE::ProverKey,
  comm_init_value: Commitment<E>,
  #[abomonate_with(<E::Scalar as PrimeField>::Repr)]
  vk_digest: E::Scalar, // digest of verifier's key
}

/// A type that represents the verifier's key
#[derive(Clone, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_bounds(where <E::Scalar as PrimeField>::Repr: Abomonation)]
pub struct VerifierKey<E: Engine, EE: EvaluationEngineTrait<E>> {
  N: usize, // table size
  vk_ee: EE::VerifierKey,
  comm_init_value: Commitment<E>,
  #[abomonation_skip]
  #[serde(skip, default = "OnceCell::new")]
  digest: OnceCell<E::Scalar>,
}

impl<E: Engine, EE: EvaluationEngineTrait<E>> VerifierKey<E, EE> {
  fn new(vk_ee: EE::VerifierKey, table_size: usize, comm_init_value: Commitment<E>) -> Self {
    VerifierKey {
      vk_ee,
      digest: Default::default(),
      comm_init_value,
      N: table_size,
    }
  }

  /// Returns the digest of the verifier's key
  pub fn digest(&self) -> E::Scalar {
    self
      .digest
      .get_or_try_init(|| {
        let dc = DigestComputer::new(self);
        dc.digest()
      })
      .cloned()
      .expect("Failure to retrieve digest!")
  }
}

impl<E: Engine, EE: EvaluationEngineTrait<E>> SimpleDigestible for VerifierKey<E, EE> {}

/// LookupSNARK
pub struct LookupSNARK<E: Engine, EE: EvaluationEngineTrait<E>> {
  a: PhantomData<(E, EE)>,

  // commitment to oracles for the inner sum-check
  comm_final_counter: CompressedCommitment<E>,
  comm_final_value: CompressedCommitment<E>,

  comm_output_arr: [CompressedCommitment<E>; 2],
  claims_product_arr: [E::Scalar; 2],

  eval_left_arr: [E::Scalar; 2],
  eval_right_arr: [E::Scalar; 2],
  eval_output_arr: [E::Scalar; 2],
  eval_input_arr: [E::Scalar; 2],
  eval_output2_arr: [E::Scalar; 2],

  // satisfiability sum-check
  sc_sat: SumcheckProof<E>,

  eval_init_value_at_r_prod: E::Scalar,
  eval_final_value_at_r_prod: E::Scalar,
  eval_final_counter_at_r_prod: E::Scalar,

  // batch openings of all multilinear polynomials
  sc_proof_batch: SumcheckProof<E>,
  evals_batch_arr: [E::Scalar; 4],
  eval_arg: EE::EvaluationArgument,
}

impl<E: Engine, EE: EvaluationEngineTrait<E>> LookupSNARK<E, EE>
where
  <E::Scalar as PrimeField>::Repr: Abomonation,
{
  /// setup
  pub fn setup(
    ck: &CommitmentKey<E>,
    initial_table: &Lookup<E::Scalar>,
  ) -> Result<(ProverKey<E, EE>, VerifierKey<E, EE>), NovaError> {
    // check the provided commitment key meets minimal requirements
    // assert!(ck.length() >= Self::commitment_key_floor()(S));
    let init_values: Vec<<E as Engine>::Scalar> = initial_table
      .into_iter()
      .map(|(_, (value, _))| *value)
      .collect();

    let comm_init_value = E::CE::commit(ck, &init_values);

    let (pk_ee, vk_ee) = EE::setup(ck);
    let table_size = initial_table.table_size();

    let vk = VerifierKey::new(vk_ee, table_size, comm_init_value);

    let pk = ProverKey {
      pk_ee,
      comm_init_value,
      vk_digest: vk.digest(),
    };

    Ok((pk, vk))
  }
  /// produces a succinct proof of satisfiability of a `LookupSNARK` instance
  #[tracing::instrument(skip_all, name = "LookupSNARK::prove")]
  pub fn prove(
    ck: &CommitmentKey<E>,
    pk: &ProverKey<E, EE>,
    challenges: (E::Scalar, E::Scalar),
    read_row: E::Scalar,
    write_row: E::Scalar,
    initial_table: &Lookup<E::Scalar>,
    final_table: &Lookup<E::Scalar>,
  ) -> Result<Self, NovaError> {
    // a list of polynomial evaluation claims that will be batched
    let mut w_u_vec = Vec::new();

    let (fingerprint_alpha, fingerprint_gamma) = challenges;
    let gamma_square: <E as Engine>::Scalar = fingerprint_gamma * fingerprint_gamma;
    let hash_func = |addr: &E::Scalar, val: &E::Scalar, ts: &E::Scalar| -> E::Scalar {
      fingerprint_alpha - (*ts * gamma_square + *val * fingerprint_gamma + *addr)
    };
    // init_row
    let initial_row: Vec<E::Scalar> = initial_table
      .into_iter()
      .map(|(addr, (value, counter))| hash_func(addr, value, counter))
      .collect();
    // audit_row
    let audit_row: Vec<E::Scalar> = final_table
      .into_iter()
      .map(|(addr, (value, counter))| hash_func(addr, value, counter))
      .collect();
    let mut transcript = E::TE::new(b"LookupSNARK");
    // append the verifier key (which includes commitment to R1CS matrices) and the read_row/write_row to the transcript
    transcript.absorb(b"vk", &pk.vk_digest);
    transcript.absorb(b"read_row", &read_row);
    transcript.absorb(b"write_row", &write_row);
    transcript.absorb(b"alpha", &fingerprint_alpha);
    transcript.absorb(b"gamma", &fingerprint_gamma);

    let init_values: Vec<<E as Engine>::Scalar> = initial_table
      .into_iter()
      .map(|(_, (value, _))| *value)
      .collect();
    let (final_values, final_counters): (Vec<_>, Vec<_>) = final_table.values().copied().unzip();
    let comm_init_value = pk.comm_init_value;
    let (comm_final_value, comm_final_counter) = rayon::join(
      || E::CE::commit(ck, &final_values),
      || E::CE::commit(ck, &final_counters),
    );
    // add commitment into the challenge
    transcript.absorb(b"e", &[comm_final_value, comm_final_counter].as_slice());

    let mut product_sc_inst =
      ProductSumcheckInstance::<E>::new(ck, vec![initial_row, audit_row], &mut transcript).unwrap();

    // sanity check: claimed_prod_init_row * write_row - claimed_prod_audit_row * read_row = 0
    let prod_claims = product_sc_inst.claims.clone();
    let (claimed_prod_init_row, claimed_prod_audit_row) = (prod_claims[0], prod_claims[1]);
    assert_eq!(claimed_prod_init_row * write_row - read_row * claimed_prod_audit_row, <E as Engine>::Scalar::ZERO, "claimed_prod_init_row {:?} * write_row {:?} -  claimed_prod_audit_row {:?} * read_row {:?} = {:?}",
      claimed_prod_init_row,
      write_row,
      claimed_prod_audit_row,
      read_row,
      claimed_prod_init_row * write_row - read_row * claimed_prod_audit_row
    );

    // generate sumcheck proof
    let initial_claims = product_sc_inst.initial_claims();
    let num_claims = initial_claims.len();
    let coeffs = {
      let s = transcript.squeeze(b"r").unwrap();
      let mut s_vec = vec![s];
      for i in 1..num_claims {
        s_vec.push(s_vec[i - 1] * s);
      }
      s_vec
    };
    // compute the joint claim
    let claim = initial_claims
      .iter()
      .zip(coeffs.iter())
      .map(|(c_1, c_2)| *c_1 * c_2)
      .sum();
    let mut e = claim;
    let mut r_sat: Vec<E::Scalar> = Vec::new();
    let mut cubic_polys: Vec<CompressedUniPoly<E::Scalar>> = Vec::new();
    let num_rounds = product_sc_inst.size().log_2();

    for _i in 0..num_rounds {
      let mut evals: Vec<Vec<E::Scalar>> = Vec::new();
      evals.extend(product_sc_inst.evaluation_points());

      let evals_combined_0 = (0..evals.len()).map(|i| evals[i][0] * coeffs[i]).sum();
      let evals_combined_2 = (0..evals.len()).map(|i| evals[i][1] * coeffs[i]).sum();
      let evals_combined_3 = (0..evals.len()).map(|i| evals[i][2] * coeffs[i]).sum();

      let evals = vec![
        evals_combined_0,
        e - evals_combined_0,
        evals_combined_2,
        evals_combined_3,
      ];
      let poly = UniPoly::from_evals(&evals);

      // append the prover's message to the transcript
      transcript.absorb(b"p", &poly);

      // derive the verifier's challenge for the next round
      let r_i = transcript.squeeze(b"c").unwrap();
      r_sat.push(r_i);

      product_sc_inst.bound(&r_i);

      e = poly.evaluate(&r_i);
      cubic_polys.push(poly.compress());
    }
    let final_claims = product_sc_inst.final_claims();

    let sc_sat = SumcheckProof::<E>::new(cubic_polys);

    // claims[0] is about the Eq polynomial, which the verifier computes directly
    // claims[1] =? weighed sum of left(rand)
    // claims[2] =? weighted sum of right(rand)
    // claims[3] =? weighted sum of output(rand), which is easy to verify by querying output
    // we also need to prove that output(output.len()-2) = claimed_product
    let eval_left_vec = final_claims[1].clone();
    let eval_right_vec = final_claims[2].clone();
    let eval_output_vec = final_claims[3].clone();

    let eval_vec = [
      eval_left_vec.clone(),
      eval_right_vec.clone(),
      eval_output_vec.clone(),
    ]
    .concat();
    // absorb all the claimed evaluations
    transcript.absorb(b"e", &eval_vec.as_slice());

    // we now combine eval_left = left(rand) and eval_right = right(rand)
    // into claims about input and output
    let c = transcript.squeeze(b"c").unwrap();

    // eval = (E::Scalar::ONE - c) * eval_left + c * eval_right
    // eval is claimed evaluation of input||output(r, c), which can be proven by proving input(r[1..], c) and output(r[1..], c)
    let rand_ext = {
      let mut r = r_sat.clone();
      r.extend(&[c]);
      r
    };
    let r_prod = rand_ext[1..].to_vec();

    let eval_input_vec = product_sc_inst
      .input_vec
      .iter()
      .map(|i| MultilinearPolynomial::evaluate_with(i, &r_prod))
      .collect::<Vec<E::Scalar>>();

    let eval_output2_vec = product_sc_inst
      .output_vec
      .iter()
      .map(|o| MultilinearPolynomial::evaluate_with(o, &r_prod))
      .collect::<Vec<E::Scalar>>();

    // add claimed evaluations to the transcript
    let evals = eval_input_vec
      .clone()
      .into_iter()
      .chain(eval_output2_vec.clone())
      .collect::<Vec<E::Scalar>>();
    transcript.absorb(b"e", &evals.as_slice());

    // squeeze a challenge to combine multiple claims into one
    let powers_of_rho = {
      let s = transcript.squeeze(b"r")?;
      let mut s_vec = vec![s];
      for i in 1..product_sc_inst.initial_claims().len() {
        s_vec.push(s_vec[i - 1] * s);
      }
      s_vec
    };

    // take weighted sum (random linear combination) of input, output, and their commitments
    // product is `initial claim`
    let product: <E as Engine>::Scalar = prod_claims
      .to_vec()
      .iter()
      .zip(powers_of_rho.iter())
      .map(|(e, p)| *e * p)
      .sum();

    let eval_output: <E as Engine>::Scalar = eval_output_vec
      .iter()
      .zip(powers_of_rho.iter())
      .map(|(e, p)| *e * p)
      .sum();

    let comm_output = product_sc_inst
      .comm_output_vec
      .iter()
      .zip(powers_of_rho.iter())
      .map(|(c, r_i)| *c * *r_i)
      .fold(Commitment::<E>::default(), |acc, item| acc + item);

    let weighted_sum = |W: &[Vec<E::Scalar>], s: &[E::Scalar]| -> Vec<E::Scalar> {
      assert_eq!(W.len(), s.len());
      let mut p = vec![<E as Engine>::Scalar::ZERO; W[0].len()];
      for i in 0..W.len() {
        for (j, item) in W[i].iter().enumerate().take(W[i].len()) {
          p[j] += *item * s[i]
        }
      }
      p
    };

    let poly_output = weighted_sum(&product_sc_inst.output_vec, &powers_of_rho);

    let eval_output2: <E as Engine>::Scalar = eval_output2_vec
      .iter()
      .zip(powers_of_rho.iter())
      .map(|(e, p)| *e * p)
      .sum();

    // eval_output = output(r_sat)
    w_u_vec.push((
      PolyEvalWitness::<E> {
        p: poly_output.clone(),
      },
      PolyEvalInstance::<E> {
        c: comm_output,
        x: r_sat.clone(),
        e: eval_output,
      },
    ));

    // claimed_product = output(1, ..., 1, 0)
    let x = {
      let mut x = vec![E::Scalar::ONE; r_sat.len()];
      x[r_sat.len() - 1] = E::Scalar::ZERO;
      x
    };
    w_u_vec.push((
      PolyEvalWitness {
        p: poly_output.clone(),
      },
      PolyEvalInstance {
        c: comm_output,
        x,
        e: product,
      },
    ));

    // eval_output2 = output(r_prod)
    w_u_vec.push((
      PolyEvalWitness { p: poly_output },
      PolyEvalInstance {
        c: comm_output,
        x: r_prod.clone(),
        e: eval_output2,
      },
    ));

    let evals = [
      &init_values, // init value (all init ts are 0)
      &final_values,
      &final_counters,
    ]
    .into_par_iter()
    .map(|p| MultilinearPolynomial::evaluate_with(p, &r_prod.clone()))
    .collect::<Vec<E::Scalar>>();

    let eval_init_value_at_r_prod = evals[0];
    let eval_final_value_at_r_prod = evals[1];
    let eval_final_counter_at_r_prod = evals[2];

    // we can batch all the claims
    transcript.absorb(
      b"e",
      &[
        eval_init_value_at_r_prod,
        eval_final_value_at_r_prod,
        eval_final_counter_at_r_prod,
      ]
      .as_slice(),
    );

    // generate challenge for rlc
    let c = transcript.squeeze(b"c")?;
    let eval_vec = [
      eval_init_value_at_r_prod,
      eval_final_value_at_r_prod,
      eval_final_counter_at_r_prod,
    ];
    let comm_vec = [comm_init_value, comm_final_value, comm_final_counter];
    let poly_vec = [
      &init_values.to_vec(),
      &final_values.to_vec(),
      &final_counters.to_vec(),
    ];
    let w = PolyEvalWitness::batch(&poly_vec, &c);
    let u = PolyEvalInstance::batch(&comm_vec, &r_prod, &eval_vec, &c);

    // add the claim to prove for later
    w_u_vec.push((w, u));

    // We will now reduce a vector of claims of evaluations at different points into claims about them at the same point.
    // For example, eval_W =? W(r_y[1..]) and eval_W =? E(r_x) into
    // two claims: eval_W_prime =? W(rz) and eval_E_prime =? E(rz)
    // We can them combine the two into one: eval_W_prime + gamma * eval_E_prime =? (W + gamma*E)(rz),
    // where gamma is a public challenge
    // Since commitments to W and E are homomorphic, the verifier can compute a commitment
    // to the batched polynomial.
    assert!(w_u_vec.len() >= 2);

    let (w_vec, u_vec): (Vec<PolyEvalWitness<E>>, Vec<PolyEvalInstance<E>>) =
      w_u_vec.into_iter().unzip();
    let w_vec_padded = PolyEvalWitness::pad(&w_vec); // pad the polynomials to be of the same size
    let u_vec_padded = PolyEvalInstance::pad(&u_vec); // pad the evaluation points

    // generate a challenge
    let rho = transcript.squeeze(b"r")?;
    let num_claims = w_vec_padded.len();
    let powers_of_rho = powers::<E>(&rho, num_claims);
    let claim_batch_joint: <E as Engine>::Scalar = u_vec_padded
      .iter()
      .zip(powers_of_rho.iter())
      .map(|(u, p)| u.e * p)
      .sum();

    let mut polys_left: Vec<MultilinearPolynomial<E::Scalar>> = w_vec_padded
      .iter()
      .map(|w| MultilinearPolynomial::new(w.p.clone()))
      .collect();
    let mut polys_right: Vec<MultilinearPolynomial<E::Scalar>> = u_vec_padded
      .iter()
      .map(|u| MultilinearPolynomial::new(EqPolynomial::new(u.x.clone()).evals()))
      .collect();

    let num_rounds_z = u_vec_padded[0].x.len();
    let comb_func = |poly_A_comp: &E::Scalar, poly_B_comp: &E::Scalar| -> E::Scalar {
      *poly_A_comp * *poly_B_comp
    };
    let (sc_proof_batch, r_z, claims_batch) = SumcheckProof::<E>::prove_quad_batch(
      &claim_batch_joint,
      num_rounds_z,
      &mut polys_left,
      &mut polys_right,
      &powers_of_rho,
      comb_func,
      &mut transcript,
    )?;

    let (claims_batch_left, _): (Vec<E::Scalar>, Vec<E::Scalar>) = claims_batch;

    transcript.absorb(b"l", &claims_batch_left.as_slice());

    // we now combine evaluation claims at the same point rz into one
    let gamma = transcript.squeeze(b"g")?;
    let powers_of_gamma: Vec<E::Scalar> = powers::<E>(&gamma, num_claims);
    let comm_joint = u_vec_padded
      .iter()
      .zip(powers_of_gamma.iter())
      .map(|(u, g_i)| u.c * *g_i)
      .fold(Commitment::<E>::default(), |acc, item| acc + item);
    let poly_joint = PolyEvalWitness::weighted_sum(&w_vec_padded, &powers_of_gamma);
    let eval_joint: <E as Engine>::Scalar = claims_batch_left
      .iter()
      .zip(powers_of_gamma.iter())
      .map(|(e, g_i)| *e * *g_i)
      .sum();

    let eval_arg = EE::prove(
      ck,
      &pk.pk_ee,
      &mut transcript,
      &comm_joint,
      &poly_joint.p,
      &r_z,
      &eval_joint,
    )?;

    Ok(LookupSNARK {
      comm_final_counter: comm_final_counter.compress(),
      comm_final_value: comm_final_value.compress(),

      comm_output_arr: vec_to_arr(
        product_sc_inst
          .comm_output_vec
          .iter()
          .map(|c| c.compress())
          .collect::<Vec<CompressedCommitment<E>>>(),
      ),
      claims_product_arr: vec_to_arr(prod_claims),

      sc_sat,

      eval_left_arr: vec_to_arr(eval_left_vec),
      eval_right_arr: vec_to_arr(eval_right_vec),
      eval_output_arr: vec_to_arr(eval_output_vec),
      eval_input_arr: vec_to_arr(eval_input_vec),
      eval_output2_arr: vec_to_arr(eval_output2_vec),

      eval_init_value_at_r_prod,
      eval_final_value_at_r_prod,
      eval_final_counter_at_r_prod,

      sc_proof_batch,
      evals_batch_arr: vec_to_arr(claims_batch_left),
      eval_arg,
      a: PhantomData {},
    })
  }

  fn verify_challenge<E2: Engine>(
    comm_final_value: <<E as Engine>::CE as CommitmentEngineTrait<E>>::Commitment,
    comm_final_counter: <<E as Engine>::CE as CommitmentEngineTrait<E>>::Commitment,
    fingerprint_intermediate_gamma: E::Scalar,
    challenges: (E::Scalar, E::Scalar),
  ) -> Result<(), NovaError>
  where
    E: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E as Engine>::Scalar>,
  {
    // verify fingerprint challenge
    let (fingerprint_alpha, fingerprint_gamma) = challenges;

    let ro_consts =
      <<E as Engine>::RO as ROTrait<<E as Engine>::Base, <E as Engine>::Scalar>>::Constants::default();

    let mut hasher = <E as Engine>::RO::new(ro_consts.clone(), 7);
    let fingerprint_intermediate_gamma: E2::Scalar =
      scalar_as_base::<E>(fingerprint_intermediate_gamma);
    hasher.absorb(fingerprint_intermediate_gamma);
    comm_final_value.absorb_in_ro(&mut hasher);
    comm_final_counter.absorb_in_ro(&mut hasher);
    let computed_gamma = hasher.squeeze(NUM_CHALLENGE_BITS);
    if fingerprint_gamma != computed_gamma {
      return Err(NovaError::InvalidMultisetProof);
    }
    let mut hasher = <E as Engine>::RO::new(ro_consts, 1);
    hasher.absorb(scalar_as_base::<E>(computed_gamma));
    let computed_alpha = hasher.squeeze(NUM_CHALLENGE_BITS);
    if fingerprint_alpha != computed_alpha {
      return Err(NovaError::InvalidMultisetProof);
    }
    Ok(())
  }

  /// verifies a proof of satisfiability of a `RelaxedR1CS` instance
  pub fn verify<E2: Engine>(
    &self,
    vk: &VerifierKey<E, EE>,
    fingerprint_intermediate_gamma: E::Scalar,
    read_row: E::Scalar,
    write_row: E::Scalar,
    challenges: (E::Scalar, E::Scalar),
  ) -> Result<(), NovaError>
  where
    E: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E as Engine>::Scalar>,
  {
    let (fingerprint_alpha, fingerprint_gamma) = challenges;
    let comm_final_value = Commitment::<E>::decompress(&self.comm_final_value)?;
    let comm_final_counter = Commitment::<E>::decompress(&self.comm_final_counter)?;

    Self::verify_challenge::<E2>(
      comm_final_value,
      comm_final_counter,
      fingerprint_intermediate_gamma,
      challenges,
    )?;

    let mut transcript = E::TE::new(b"LookupSNARK");
    let mut u_vec: Vec<PolyEvalInstance<E>> = Vec::new();

    // append the verifier key (including commitment to R1CS matrices) and the RelaxedR1CSInstance to the transcript
    transcript.absorb(b"vk", &vk.digest());
    transcript.absorb(b"read_row", &read_row);
    transcript.absorb(b"write_row", &write_row);
    transcript.absorb(b"alpha", &fingerprint_alpha);
    transcript.absorb(b"gamma", &fingerprint_gamma);

    // add commitment into the challenge
    transcript.absorb(b"e", &[comm_final_value, comm_final_counter].as_slice());

    let num_rounds_sat = vk.N.log_2();

    // hash function
    let gamma_square = fingerprint_gamma * fingerprint_gamma;
    let hash_func = |addr: &E::Scalar, val: &E::Scalar, ts: &E::Scalar| -> E::Scalar {
      fingerprint_alpha - (*ts * gamma_square + *val * fingerprint_gamma + *addr)
    };

    // check claimed_prod_init_row * write_row - claimed_prod_audit_row * read_row = 0
    // sanity check: any of them might not be 0
    assert!(
      self.claims_product_arr[0] * write_row * self.claims_product_arr[1] * read_row
        != E::Scalar::ZERO,
      "any of claims_product_arr {:?}, write_row {:?}, read_row {:?} = 0",
      self.claims_product_arr,
      write_row,
      read_row
    );
    if self.claims_product_arr[0] * write_row - self.claims_product_arr[1] * read_row
      != E::Scalar::ZERO
    {
      return Err(NovaError::InvalidMultisetProof);
    }

    let comm_output_vec = self
      .comm_output_arr
      .iter()
      .map(|c| Commitment::<E>::decompress(c))
      .collect::<Result<Vec<Commitment<E>>, NovaError>>()?;

    transcript.absorb(b"o", &comm_output_vec.as_slice());
    transcript.absorb(b"c", &self.claims_product_arr.as_slice());

    let num_rounds = vk.N.log_2();
    let rand_eq = (0..num_rounds)
      .map(|_i| transcript.squeeze(b"e"))
      .collect::<Result<Vec<E::Scalar>, NovaError>>()?;

    let num_claims = 2;
    let coeffs = {
      let s = transcript.squeeze(b"r")?;
      let mut s_vec = vec![s];
      for i in 1..num_claims {
        s_vec.push(s_vec[i - 1] * s);
      }
      s_vec
    };

    let (claim_mem_sat_final, r_sat) =
      self
        .sc_sat
        .verify(E::Scalar::ZERO, num_rounds_sat, 3, &mut transcript)?;
    let rand_eq_bound_r_sat = EqPolynomial::new(rand_eq).evaluate(&r_sat);
    let claim_mem_final_expected: E::Scalar = (0..2)
      .map(|i| {
        coeffs[i]
          * rand_eq_bound_r_sat
          * (self.eval_left_arr[i] * self.eval_right_arr[i] - self.eval_output_arr[i])
      })
      .sum();

    if claim_mem_final_expected != claim_mem_sat_final {
      return Err(NovaError::InvalidSumcheckProof);
    }

    // claims from the end of the sum-check
    let eval_vec = []
      .into_iter()
      .chain(self.eval_left_arr)
      .chain(self.eval_right_arr)
      .chain(self.eval_output_arr)
      .collect::<Vec<E::Scalar>>();

    transcript.absorb(b"e", &eval_vec.as_slice());
    // we now combine eval_left = left(rand) and eval_right = right(rand)
    // into claims about input and output
    let c = transcript.squeeze(b"c")?;

    // eval = (E::Scalar::ONE - c) * eval_left + c * eval_right
    // eval is claimed evaluation of input||output(r, c), which can be proven by proving input(r[1..], c) and output(r[1..], c)
    let rand_ext = {
      let mut r = r_sat.clone();
      r.extend(&[c]);
      r
    };
    let r_prod = rand_ext[1..].to_vec();

    // add claimed evaluations to the transcript
    let evals = self
      .eval_input_arr
      .into_iter()
      .chain(self.eval_output2_arr)
      .collect::<Vec<E::Scalar>>();
    transcript.absorb(b"e", &evals.as_slice());

    // squeeze a challenge to combine multiple claims into one
    let powers_of_rho = {
      let s = transcript.squeeze(b"r")?;
      let mut s_vec = vec![s];
      for i in 1..num_claims {
        s_vec.push(s_vec[i - 1] * s);
      }
      s_vec
    };

    // take weighted sum of input, output, and their commitments
    let product = self
      .claims_product_arr
      .iter()
      .zip(powers_of_rho.iter())
      .map(|(e, p)| *e * p)
      .sum();

    let eval_output = self
      .eval_output_arr
      .iter()
      .zip(powers_of_rho.iter())
      .map(|(e, p)| *e * p)
      .sum();

    let comm_output = comm_output_vec
      .iter()
      .zip(powers_of_rho.iter())
      .map(|(c, r_i)| *c * *r_i)
      .fold(Commitment::<E>::default(), |acc, item| acc + item);

    let eval_output2 = self
      .eval_output2_arr
      .iter()
      .zip(powers_of_rho.iter())
      .map(|(e, p)| *e * p)
      .sum();

    // eval_output = output(r_sat)
    u_vec.push(PolyEvalInstance {
      c: comm_output,
      x: r_sat.clone(),
      e: eval_output,
    });

    // claimed_product = output(1, ..., 1, 0)
    let x = {
      let mut x = vec![E::Scalar::ONE; r_sat.len()];
      x[r_sat.len() - 1] = E::Scalar::ZERO;
      x
    };
    u_vec.push(PolyEvalInstance {
      c: comm_output,
      x,
      e: product,
    });

    // eval_output2 = output(r_prod)
    u_vec.push(PolyEvalInstance {
      c: comm_output,
      x: r_prod.clone(),
      e: eval_output2,
    });

    // we can batch all the claims
    transcript.absorb(
      b"e",
      &[
        self.eval_init_value_at_r_prod,
        self.eval_final_value_at_r_prod,
        self.eval_final_counter_at_r_prod,
      ]
      .as_slice(),
    );
    let c = transcript.squeeze(b"c")?;
    let eval_vec = [
      self.eval_init_value_at_r_prod,
      self.eval_final_value_at_r_prod,
      self.eval_final_counter_at_r_prod,
    ];
    let comm_vec = vec![vk.comm_init_value, comm_final_value, comm_final_counter];
    let u = PolyEvalInstance::batch(&comm_vec, &r_prod, &eval_vec, &c);

    // add the claim to prove for later
    u_vec.push(u);

    // finish the final step of the sum-check
    let (claim_init_expected_row, claim_audit_expected_row) = {
      let addr = IdentityPolynomial::new(r_prod.len()).evaluate(&r_prod);
      (
        hash_func(&addr, &self.eval_init_value_at_r_prod, &E::Scalar::ZERO),
        hash_func(
          &addr,
          &self.eval_final_value_at_r_prod,
          &self.eval_final_counter_at_r_prod,
        ),
      )
    };

    // multiset check for the row
    if claim_init_expected_row != self.eval_input_arr[0]
      || claim_audit_expected_row != self.eval_input_arr[1]
    {
      return Err(NovaError::InvalidSumcheckProof);
    }

    let u_vec_padded = PolyEvalInstance::pad(&u_vec); // pad the evaluation points

    // generate a challenge
    let rho = transcript.squeeze(b"r")?;
    let num_claims = u_vec.len();
    let powers_of_rho = powers::<E>(&rho, num_claims);
    let claim_batch_joint = u_vec_padded
      .iter()
      .zip(powers_of_rho.iter())
      .map(|(u, p)| u.e * p)
      .sum();

    let num_rounds_z = u_vec_padded[0].x.len();
    let (claim_batch_final, r_z) =
      self
        .sc_proof_batch
        .verify(claim_batch_joint, num_rounds_z, 2, &mut transcript)?;

    let claim_batch_final_expected = {
      let poly_rz = EqPolynomial::new(r_z.clone());
      let evals = u_vec_padded.iter().map(|u| poly_rz.evaluate(&u.x));

      evals
        .zip(self.evals_batch_arr.iter())
        .zip(powers_of_rho.iter())
        .map(|((e_i, p_i), rho_i)| e_i * *p_i * rho_i)
        .sum()
    };

    if claim_batch_final != claim_batch_final_expected {
      return Err(NovaError::InvalidSumcheckProof);
    }

    transcript.absorb(b"l", &self.evals_batch_arr.as_slice());

    // we now combine evaluation claims at the same point rz into one
    let gamma = transcript.squeeze(b"g")?;
    let powers_of_gamma: Vec<E::Scalar> = powers::<E>(&gamma, num_claims);
    let comm_joint = u_vec_padded
      .iter()
      .zip(powers_of_gamma.iter())
      .map(|(u, g_i)| u.c * *g_i)
      .fold(Commitment::<E>::default(), |acc, item| acc + item);
    let eval_joint = self
      .evals_batch_arr
      .iter()
      .zip(powers_of_gamma.iter())
      .map(|(e, g_i)| *e * *g_i)
      .sum();

    // verify
    EE::verify(
      &vk.vk_ee,
      &mut transcript,
      &comm_joint,
      &r_z,
      &eval_joint,
      &self.eval_arg,
    )?;

    Ok(())
  }
}
