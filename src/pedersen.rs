use ark_ec::{CurveGroup, Group};
use ark_std::{
    rand::{Rng, RngCore},
    UniformRand,
};
use std::marker::PhantomData;

use crate::utils::{naive_msm, vec_add, vector_elem_product};

use crate::transcript::Transcript;
use ark_crypto_primitives::sponge::Absorb;

pub struct Proof_elem<C: CurveGroup> {
    R: C,
    t1: C::ScalarField,
    t2: C::ScalarField,
}
pub struct Proof<C: CurveGroup> {
    R: C,
    u_: Vec<C::ScalarField>,
    ru_: C::ScalarField,
}

pub struct Params<C: CurveGroup> {
    g: C,
    h: C,
    pub generators: Vec<C>,
}

pub struct Pedersen<C: CurveGroup>
where
    <C as Group>::ScalarField: Absorb,
    <C as CurveGroup>::BaseField: Absorb,
{
    _c: PhantomData<C>,
}

impl<C: CurveGroup> Pedersen<C>
where
    <C as Group>::ScalarField: Absorb,
    <C as CurveGroup>::BaseField: Absorb,
{
    pub fn new_params<R: Rng>(rng: &mut R, max: usize) -> Params<C> {
        let h_scalar = C::ScalarField::rand(rng);
        let g: C = C::generator();
        let generators: Vec<C> = vec![C::rand(rng); max];
        let params: Params<C> = Params::<C> {
            g,
            h: g.mul(h_scalar),
            generators,
        };
        params
    }

    pub fn commit_elem<R: RngCore>(
        rng: &mut R,
        params: &Params<C>,
        v: &C::ScalarField,
    ) -> CommitmentElem<C> {
        // Pedersen Commitment
        // cm = g^v * h^r
        let r = C::ScalarField::rand(rng);
        let cm: C = params.g.mul(v) + params.h.mul(r);
        CommitmentElem::<C> { cm, r }
    }
    pub fn commit(
        params: &Params<C>,
        v: &Vec<C::ScalarField>,
        r: &C::ScalarField, // random value is provided, in order to be choosen by other parts of the protocol
    ) -> Commitment<C> {
        // cm = h^r * g^v
        // where g is a generator, r is a random point
        let cm = params.h.mul(r) + naive_msm(v, &params.generators);
        Commitment::<C>(cm)
    }

    pub fn prove_elem(
        params: &Params<C>,
        transcript: &mut Transcript<C::ScalarField, C>,
        cm: C,
        v: C::ScalarField,
        r: C::ScalarField,
    ) -> Proof_elem<C> {
        // R: g^r1 * h^r2
        // t1: r1 + v * e
        // t2: r2 + r * e
        // verify: R =? cm^e * g^t1 * h^t2

        let r1 = transcript.get_challenge();
        let r2 = transcript.get_challenge();

        let R: C = params.g.mul(r1) + params.h.mul(r2);

        transcript.add_point(&cm);
        transcript.add_point(&R);
        let e = transcript.get_challenge();

        let t1 = r1 + v * e;
        let t2 = r2 + r * e;

        Proof_elem::<C> { R, t1, t2 }
    }
    pub fn prove(
        params: &Params<C>,
        transcript: &mut Transcript<C::ScalarField, C>,
        cm: &Commitment<C>, // TODO maybe it makes sense to not have a type wrapper and use directly C
        v: &Vec<C::ScalarField>,
        r: &C::ScalarField,
    ) -> Proof<C> {
        let r1 = transcript.get_challenge();
        let d = transcript.get_challenge_vec(v.len());

        let R: C = params.h.mul(r1) + naive_msm(&d, &params.generators);

        transcript.add_point(&cm.0);
        transcript.add_point(&R);
        let e = transcript.get_challenge();

        let u_ = vec_add(&vector_elem_product(v, &e), &d);
        let ru_ = e * r + r1;

        Proof::<C> { R, u_, ru_ }
    }
    pub fn verify(
        params: &Params<C>,
        transcript: &mut Transcript<C::ScalarField, C>,
        cm: Commitment<C>,
        proof: Proof<C>,
    ) -> bool {
        // r1, d just to match Prover's transcript
        transcript.get_challenge(); // r_1
        transcript.get_challenge_vec(proof.u_.len()); // d

        transcript.add_point(&cm.0);
        transcript.add_point(&proof.R);
        let e = transcript.get_challenge();
        let lhs = proof.R + cm.0.mul(e);
        let rhs = params.h.mul(proof.ru_) + naive_msm(&proof.u_, &params.generators);
        if lhs != rhs {
            return false;
        }
        true
    }

    pub fn verify_elem(
        params: &Params<C>,
        transcript: &mut Transcript<C::ScalarField, C>,
        cm: C,
        proof: Proof_elem<C>,
    ) -> bool {
        // s1, s2 just to match Prover's transcript
        transcript.get_challenge(); // r_1
        transcript.get_challenge(); // r_2

        transcript.add_point(&cm);
        transcript.add_point(&proof.R);
        let e = transcript.get_challenge();
        let lhs = proof.R + cm.mul(e);
        let rhs = params.g.mul(proof.t1) + params.h.mul(proof.t2);
        if lhs != rhs {
            return false;
        }
        true
    }
}

#[derive(Clone, Debug)]
pub struct Commitment<C: CurveGroup>(pub C);

pub struct CommitmentElem<C: CurveGroup> {
    pub cm: C,
    pub r: C::ScalarField,
}
impl<C: CurveGroup> CommitmentElem<C>
where
    <C as Group>::ScalarField: Absorb,
    <C as CurveGroup>::BaseField: Absorb,
{
    pub fn prove(
        &self,
        params: &Params<C>,
        transcript: &mut Transcript<C::ScalarField, C>,
        v: C::ScalarField,
    ) -> Proof_elem<C> {
        Pedersen::<C>::prove_elem(params, transcript, self.cm, v, self.r)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transcript::poseidon_test_config;
    use ark_mnt4_298::{Fr, G1Projective};

    #[test]
    fn test_pedersen_single_element() {
        let mut rng = ark_std::test_rng();

        // setup params
        let params = Pedersen::<G1Projective>::new_params(
            &mut rng, 0, /* 0, as here we don't use commit_vec */
        );
        let poseidon_config = poseidon_test_config::<Fr>();

        // init Prover's transcript
        let mut transcript_p = Transcript::<Fr, G1Projective>::new(&poseidon_config);
        // init Verifier's transcript
        let mut transcript_v = Transcript::<Fr, G1Projective>::new(&poseidon_config);

        let v = Fr::rand(&mut rng);

        let cm = Pedersen::commit_elem(&mut rng, &params, &v);
        let proof = cm.prove(&params, &mut transcript_p, v);
        // also can use:
        // let proof = Pedersen::prove_elem(&params, &mut transcript_p, cm.cm, v, cm.r);
        let v = Pedersen::verify_elem(&params, &mut transcript_v, cm.cm, proof);
        assert!(v);
    }
    #[test]
    fn test_pedersen_vector() {
        let mut rng = ark_std::test_rng();

        const n: usize = 10;
        // setup params
        let params = Pedersen::<G1Projective>::new_params(&mut rng, n);
        let poseidon_config = poseidon_test_config::<Fr>();

        // init Prover's transcript
        let mut transcript_p = Transcript::<Fr, G1Projective>::new(&poseidon_config);
        // init Verifier's transcript
        let mut transcript_v = Transcript::<Fr, G1Projective>::new(&poseidon_config);

        let v: Vec<Fr> = vec![Fr::rand(&mut rng); n];
        let r: Fr = Fr::rand(&mut rng);
        let cm = Pedersen::commit(&params, &v, &r);
        let proof = Pedersen::prove(&params, &mut transcript_p, &cm, &v, &r);
        let v = Pedersen::verify(&params, &mut transcript_v, cm, proof);
        assert!(v);
    }
}