use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_poly::{
    DenseMVPolynomial, DenseUVPolynomial, Polynomial,
};
use ark_crypto_primitives::sponge::Absorb;
use crate::utils::{multipoly_linear_combination};
use crate::neutronnova::sumcheck::{SumCheckProof};

#[derive(Debug)]
pub struct SumCheckRelation<F: PrimeField, MV: DenseMVPolynomial<F>> {
    pub T: F,          // Sum T
    pub w: Vec<F>, // witness w (行列)
    pub x: Vec<F>,      // input x (ベクトル)
    pub u: Vec<F>,      // commitments u
    pub g: Vec<MV>,     // 構成された多項式 g_i
    pub F: MV,          // 多項式 F
}

pub struct SumFold<
    F: PrimeField + Absorb,
    C: CurveGroup,
    UV: Polynomial<F> + DenseUVPolynomial<F>,
    MV: Polynomial<F> + DenseMVPolynomial<F>,
> {
    _f: std::marker::PhantomData<F>,
    _c: std::marker::PhantomData<C>,
    _uv: std::marker::PhantomData<UV>,
    _mv: std::marker::PhantomData<MV>,
}

impl<
    F: PrimeField + Absorb,
    C: CurveGroup,
    UV: Polynomial<F> + DenseUVPolynomial<F>,
    MV: Polynomial<F> + DenseMVPolynomial<F, Point = Vec<F>>,
> SumFold<F, C, UV, MV>
where
    <C as CurveGroup>::BaseField: Absorb,
{
    pub fn fold_unstructed(
        sc1: SumCheckProof<F, UV>,
        sc2: SumCheckProof<F, UV>,
        q1: MV,
        q2: MV,
    ) -> (F, MV) {
        let mut rng = ark_std::test_rng();
        let rho = F::rand(&mut rng);

        let T_prime = sc1.T + rho * sc2.T;
        let q_prime = multipoly_linear_combination(&q1, &q2, rho);
        
        (T_prime, q_prime)
    }

    // pub fn fold_two_sc(
    //     sc1: SumCheckRelation<F, MV>,
    //     sc2: SumCheckRelation<F, MV>,
    // ) -> SumCheckRelation<F, MV> {
    //     let T_vec = vec![sc1.T, sc2.T];
    //     let G_vec = vec![sc1.g.clone(), sc2.g.clone()]; // G_0とG_1
    //     let F_poly = sc1.f.clone(); // fはsc1のものを使用
    //     let u_vec = vec![sc1.u.clone(), sc2.u.clone()];
    //     let x_vec = vec![sc1.x[0], sc2.x[0]]; // xはスカラー
    //     let w_vec = vec![sc1.w.clone(), sc2.w.clone()];

    //     // (verifier) rho と b の選択
    //     let rho = F::rand(&mut ark_std::test_rng());
    //     let b = F::rand(&mut ark_std::test_rng());

    //     // c と r_b の計算
    //     let (c, r_b) = Self::compute_c_r(&rho, &b, &T_vec, &G_vec, &F_poly, &x_vec, &w_vec);

    //     // インスタンスと証拠の畳み込み
    //     let (T_prime, u_prime, x_prime, w_prime) = Self::compute_instance_witness_pair(
    //         c, rho, r_b, u_vec, x_vec, w_vec
    //     );

    //     // 新しいSumCheckRelationを返す
    //     SumCheckRelation::new(T_prime, u_prime, x_prime, w_prime, sc1.g.clone(), sc1.f.clone())
    // }

    // /// 2. Compute (c, rb)
    // pub fn compute_c_r(
    //     rho: &F,
    //     b: &F,
    //     T: &[F],      // T_0 and T_1 (借用)
    //     G: &[MV],     // G_0 and G_1 (借用)
    //     F_poly: &MV,  // f polynomial (借用)
    //     x: &[F],      // x (借用)
    //     w: &[Vec<F>], // w_0 and w_1 (借用)
    // ) -> (F, F) {
    //     // 1. T = \sum eq(i, rho) * T_i
    //     let mut T_sum = F::zero();
    //     let nu = T.len();
    //     for i in 0..nu {
    //         let i_val = F::from(i as u64);
    //         T_sum += Self::eq(i_val, *rho) * T[i];
    //     }

    //     // 2. f_j(b, x) = \sum eq(i, b) * g_i,j(x)
    //     let mut f_b_x_sum = vec![F::zero(); F_poly.num_vars()];
    //     for i in 0..nu {
    //         let i_val = F::from(i as u64);

    //         // G_i の評価
    //         let g_i_eval = G[i].evaluate(&[w[i].clone(), x.to_vec()].concat()); // wとxを連結して評価

    //         // f_j(b, x)の計算
    //         for j in 0..f_b_x_sum.len() {
    //             f_b_x_sum[j] += Self::eq(i_val, *b) * g_i_eval; // インデックスなしの演算に修正
    //         }
    //     }

    //     // 3. Q(b) = eq(rho, b) * (\sum F(f_1(b,x), ..., f_t(b,x)))
    //     let mut Q_b = Self::eq(*rho, *b);
    //     if Q_b == F::zero() {
    //         return (T_sum, Q_b);
    //     }

    //     let l = x.len();
    //     for x_val in 0..(1 << l) {
    //         let mut f_values = vec![F::zero(); f_b_x_sum.len()];
    //         for j in 0..f_b_x_sum.len() {
    //             let bit = if (x_val >> j) & 1 == 1 {
    //                 F::one()
    //             } else {
    //                 F::zero()
    //             };
    //             f_values[j] = f_b_x_sum[j] * bit;
    //         }

    //         // f_valuesをVec<F>として評価
    //         Q_b += F_poly.evaluate(&f_values);
    //     }

    //     (T_sum, Q_b)
    // }

    // // 3. Output the folded instance-witness pair
    // pub fn compute_instance_witness_pair(
    //     c: F,
    //     rho: F,
    //     rb: F,
    //     u: Vec<Vec<F>>,
    //     x: Vec<F>,
    //     w: Vec<Vec<F>>,
    // ) -> (F, Vec<F>, Vec<F>, Vec<F>) {
    //     // T' = c * eq(rho, rb)^(-1)
    //     // TODO: inverse???本当に???
    //     let T_prime = c * Self::eq(rho, rb);

    //     // u' = \sum eq(rb, i) * u_i
    //     let mut u_prime = vec![F::zero(); u[0].len()];
    //     let nu = u.len();
    //     for j in 0..u[0].len() {
    //         for i in 0..nu {
    //             let i_val = F::from(i as u64);
    //             u_prime[j] += Self::eq(rb, i_val) * u[i][j];
    //         }
    //     }

    //     // x' = \sum eq(rb, i) * x_i
    //     let mut x_prime = F::zero();
    //     for i in 0..x.len() {
    //         let i_val = F::from(i as u64);
    //         x_prime += Self::eq(rb, i_val) * x[i];
    //     }

    //     // w' = \sum eq(rb, i) * w_i
    //     let mut w_prime = vec![F::zero(); w[0].len()];
    //     for j in 0..w[0].len() {
    //         for i in 0..nu {
    //             let i_val = F::from(i as u64);
    //             w_prime[j] += Self::eq(rb, i_val) * w[i][j];
    //         }
    //     }

    //     (T_prime, u_prime, vec![x_prime], w_prime)
    // }

    // /// check if a == b
    // fn eq(a: F, b: F) -> F {
    //     if a == b {
    //         F::one()
    //     } else {
    //         F::zero()
    //     }
    // }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::neutronnova::sumcheck::SumCheck;
    use crate::transcript::{poseidon_test_config, Transcript};
    use ark_mnt4_298::{Fr, G1Projective};
    use ark_poly::{
        multivariate::{SparsePolynomial, SparseTerm, Term},
        univariate::DensePolynomial,
        Polynomial,
    };
    use ark_std::{rand::Rng, UniformRand, One, Zero};
    use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig};

    fn random_sc(poseidon_config: &PoseidonConfig<Fr>) -> SumCheckRelation<Fr, SparsePolynomial<Fr, SparseTerm>> {
        let mut rng = ark_std::test_rng();

        // Define the size of the test vectors and polynomials
        let n = 5; // Number of variables/polynomials

        // Generate random vectors x and w
        let x: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
        let w: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();

        // Construct multivariate polynomials g_i (as SparsePolynomials)
        let g: Vec<SparsePolynomial<Fr, SparseTerm>> = (0..n)
            .map(|_| {
                let term = SparseTerm::new(vec![(0, 1)]); // Example term x_0^1
                SparsePolynomial::from_coefficients_vec(n, vec![(Fr::one(), term)])
            })
            .collect();

        // Construct the polynomial F as a multivariate polynomial
        let mut f_terms = vec![];
        for i in 0..n {
            let term = SparseTerm::new(vec![(i, 1)]); // Example term x_i^1
            f_terms.push((Fr::rand(&mut rng), term));
        }
        let F = SparsePolynomial::from_coefficients_vec(n, f_terms);

        let mut T = Fr::zero();
        for (g_i, x_i) in g.iter().zip(&x) {
            let g_x = g_i.evaluate(&vec![*x_i]); 
            let f_g_x = F.evaluate(&vec![g_x]); 
            T += f_g_x;
        }

        let mut u: Vec<Fr> = vec![];
        for w_i in &w {
            let mut transcript = Transcript::<Fr, G1Projective>::new(&poseidon_config);
            transcript.add(w_i);
            let u_i = transcript.get_challenge();
            u.push(u_i);
        }

        SumCheckRelation {
            T,
            w: w.clone(),
            x: x.clone(),
            u: u.clone(),
            g: g.clone(),
            F: F.clone(),
        }
    }

    fn rand_poly<R: Rng>(l: usize, d: usize, rng: &mut R) -> SparsePolynomial<Fr, SparseTerm> {
        // This method is from the arkworks/algebra/poly/multivariate test:
        // https://github.com/arkworks-rs/algebra/blob/bc991d44c5e579025b7ed56df3d30267a7b9acac/poly/src/polynomial/multivariate/sparse.rs#L303
        let mut random_terms = Vec::new();
        let num_terms = rng.gen_range(1..1000);
        // For each term, randomly select up to `l` variables with degree
        // in [1,d] and random coefficient
        random_terms.push((Fr::rand(rng), SparseTerm::new(vec![])));
        for _ in 1..num_terms {
            let term = (0..l)
                .map(|i| {
                    if rng.gen_bool(0.5) {
                        Some((i, rng.gen_range(1..(d + 1))))
                    } else {
                        None
                    }
                })
                .flatten()
                .collect();
            let coeff = Fr::rand(rng);
            random_terms.push((coeff, SparseTerm::new(term)));
        }
        SparsePolynomial::from_coefficients_slice(l, &random_terms)
    }

    #[test]
    fn test_fold_unstructed_sumchecks() {
        type SC = SumCheck<Fr, G1Projective, DensePolynomial<Fr>, SparsePolynomial<Fr, SparseTerm>>;
        type SF = SumFold<Fr, G1Projective, DensePolynomial<Fr>, SparsePolynomial<Fr, SparseTerm>>;
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();
        let q1 = rand_poly(3, 3, &mut rng);
        let sc1 = SC::prove(&poseidon_config, q1.clone());
        let q2 = rand_poly(3, 3, &mut rng);
        let sc2 = SC::prove(&poseidon_config, q2.clone());

        let (T_prime, q_prime) = SF::fold_unstructed(sc1, sc2, q1, q2);
        let proof = SC::prove(&poseidon_config, q_prime.clone());
        assert_eq!(proof.T, T_prime, "Folded different SumCheckRelation failed T equality check");

        let verification_result = SC::verify(&poseidon_config, proof);
        assert!(verification_result, "Folded different SumCheckRelation failed verification");
    }

    #[test]
    fn test_abnormal_fold_unstructed_sumchecks() {
        type SC = SumCheck<Fr, G1Projective, DensePolynomial<Fr>, SparsePolynomial<Fr, SparseTerm>>;
        type SF = SumFold<Fr, G1Projective, DensePolynomial<Fr>, SparsePolynomial<Fr, SparseTerm>>;
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();
        let q1 = rand_poly(3, 3, &mut rng);
        let mut sc1 = SC::prove(&poseidon_config, q1.clone());
        sc1.T += Fr::one();
        let verification_result_sc1 = SC::verify(&poseidon_config, sc1.clone());
        assert!(!verification_result_sc1, "Abnormal SumCheckRelation failed verification");
        let q2 = rand_poly(3, 3, &mut rng);
        let sc2 = SC::prove(&poseidon_config, q2.clone());

        let (T_prime, q_prime) = SF::fold_unstructed(sc1, sc2, q1, q2);
        let proof = SC::prove(&poseidon_config, q_prime.clone());
        assert!(T_prime != proof.T, "Folded different SumCheckRelation failed T equality check");
    }

    #[test]
    fn test_fold_structured_sumchecks() {
        let poseidon_config = poseidon_test_config::<Fr>();
        let sc1 = random_sc(&poseidon_config);
        let sc2 = random_sc(&poseidon_config);
        println!("sc1.T: {:?}", sc1.T);
        println!("sc2.T: {:?}", sc2.T);
    }
}