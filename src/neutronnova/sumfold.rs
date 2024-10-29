use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_poly::{
    DenseMVPolynomial, DenseUVPolynomial, Polynomial,
};
use ark_crypto_primitives::sponge::Absorb;
use rayon::prelude::*;

// SumCheckRelation構造体の定義
pub struct SumCheckRelation<F: PrimeField, MV: DenseMVPolynomial<F>> {
    pub T: F,          // Sum T
    pub u: Vec<F>,     // instance u
    pub x: Vec<F>,     // input x
    pub w: Vec<F>,     // witness w
    pub g: MV,         // multilinear polynomial g
    pub f: MV,         // polynomial f
}

impl<F: PrimeField, MV: DenseMVPolynomial<F>> SumCheckRelation<F, MV> {
    pub fn new(T: F, u: Vec<F>, x: Vec<F>, w: Vec<F>, g: MV, f: MV) -> Self {
        SumCheckRelation { T, u, x, w, g, f }
    }
}

// SumFold構造体の定義
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
    MV: Polynomial<F> + DenseMVPolynomial<F, Point = Vec<F>>, // 型制約の追加
> SumFold<F, C, UV, MV>
where
    <C as CurveGroup>::BaseField: Absorb,
{
    /// 2つのSumCheckRelationを畳み込み、新しいSumCheckRelationを返す関数
    pub fn fold_two_sc(
        sc1: SumCheckRelation<F, MV>,
        sc2: SumCheckRelation<F, MV>,
    ) -> SumCheckRelation<F, MV> {
        let T_vec = vec![sc1.T, sc2.T];
        let G_vec = vec![sc1.g.clone(), sc2.g.clone()]; // G_0とG_1
        let F_poly = sc1.f.clone(); // fはsc1のものを使用
        let u_vec = vec![sc1.u.clone(), sc2.u.clone()];
        let x_vec = vec![sc1.x[0], sc2.x[0]]; // xはスカラー
        let w_vec = vec![sc1.w.clone(), sc2.w.clone()];

        // (verifier) rho と b の選択
        let rho = F::rand(&mut ark_std::test_rng());
        let b = F::rand(&mut ark_std::test_rng());

        // c と r_b の計算
        let (c, r_b) = Self::compute_c_r(&rho, &b, &T_vec, &G_vec, &F_poly, &x_vec, &w_vec);

        // インスタンスと証拠の畳み込み
        let (T_prime, u_prime, x_prime, w_prime) = Self::compute_instance_witness_pair(
            c, rho, r_b, u_vec, x_vec, w_vec
        );

        // 新しいSumCheckRelationを返す
        SumCheckRelation::new(T_prime, u_prime, x_prime, w_prime, sc1.g.clone(), sc1.f.clone())
    }

    /// 2. Compute (c, rb)
    pub fn compute_c_r(
        rho: &F,
        b: &F,
        T: &[F],      // T_0 and T_1 (借用)
        G: &[MV],     // G_0 and G_1 (借用)
        F_poly: &MV,  // f polynomial (借用)
        x: &[F],      // x (借用)
        w: &[Vec<F>], // w_0 and w_1 (借用)
    ) -> (F, F) {
        // 1. T = \sum eq(i, rho) * T_i
        let nu = T.len();
        let T_sum = (0..nu).into_par_iter().map(|i| {
            let i_val = F::from(i as u64);
            Self::eq(i_val, *rho) * T[i]
        }).reduce(
            || F::zero(),  
            |acc, item| acc + item
        );

        // 2. f_j(b, x) = \sum eq(i, b) * g_i,j(x)
        let f_b_x_sum_j = (0..nu).into_par_iter().map(|i| {
            let i_val = F::from(i as u64);
            // G_i の評価
            let g_i_eval = G[i].evaluate(&[w[i].clone(), x.to_vec()].concat()); // wとxを連結して評価

            // f_j(b, x)の計算
            // for j in 0..f_b_x_sum.len() {
            //     f_b_x_sum[j] += Self::eq(i_val, *b) * g_i_eval; // インデックスなしの演算に修正
            // }
            Self::eq(i_val, *b) * g_i_eval // インデックスなしの演算に修正
        }).reduce(
            || F::zero(),
            |acc, item| acc + item
        );
        let f_b_x_sum = vec![f_b_x_sum_j; F_poly.num_vars()];

        // 3. Q(b) = eq(rho, b) * (\sum F(f_1(b,x), ..., f_t(b,x)))
        let mut Q_b = Self::eq(*rho, *b);
        if Q_b == F::zero() {
            return (T_sum, Q_b);
        }

        let l = x.len();
        for x_val in 0..(1 << l) {
            let mut f_values = vec![F::zero(); f_b_x_sum.len()];
            for j in 0..f_b_x_sum.len() {
                let bit = if (x_val >> j) & 1 == 1 {
                    F::one()
                } else {
                    F::zero()
                };
                f_values[j] = f_b_x_sum[j] * bit;
            }

            // f_valuesをVec<F>として評価
            Q_b += F_poly.evaluate(&f_values);
        }

        (T_sum, Q_b)
    }

    // 3. Output the folded instance-witness pair
    pub fn compute_instance_witness_pair(
        c: F,
        rho: F,
        rb: F,
        u: Vec<Vec<F>>,
        x: Vec<F>,
        w: Vec<Vec<F>>,
    ) -> (F, Vec<F>, Vec<F>, Vec<F>) {
        // T' = c * eq(rho, rb)^(-1)
        // TODO: inverse???本当に???
        let T_prime = c * Self::eq(rho, rb);

        // u' = \sum eq(rb, i) * u_i
        let mut u_prime = vec![F::zero(); u[0].len()];
        let nu = u.len();
        for j in 0..u[0].len() {
            for i in 0..nu {
                let i_val = F::from(i as u64);
                u_prime[j] += Self::eq(rb, i_val) * u[i][j];
            }
        }

        // x' = \sum eq(rb, i) * x_i
        let mut x_prime = F::zero();
        for i in 0..x.len() {
            let i_val = F::from(i as u64);
            x_prime += Self::eq(rb, i_val) * x[i];
        }

        // w' = \sum eq(rb, i) * w_i
        let mut w_prime = vec![F::zero(); w[0].len()];
        for j in 0..w[0].len() {
            for i in 0..nu {
                let i_val = F::from(i as u64);
                w_prime[j] += Self::eq(rb, i_val) * w[i][j];
            }
        }

        (T_prime, u_prime, vec![x_prime], w_prime)
    }

    /// aとbが等しいかをチェックする関数
    fn eq(a: F, b: F) -> F {
        if a == b {
            F::one()
        } else {
            F::zero()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::neutronnova::sumcheck::SumCheck;
    use crate::transcript::poseidon_test_config;
    use ark_mnt4_298::{Fr, G1Projective}; // scalar field
    use ark_poly::{
        multivariate::{SparsePolynomial, SparseTerm, Term},
        univariate::DensePolynomial,
        DenseMVPolynomial,
    };
    use ark_std::{rand::Rng, UniformRand};

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
    fn test_fold_and_verify_sumcheck() {
        let mut rng = ark_std::test_rng();

        // 1つ目のランダムな多項式を生成
        let g1 = rand_poly(3, 3, &mut rng);
        let f1 = rand_poly(3, 2, &mut rng);

        // 2つ目のランダムな多項式を生成
        let g2 = rand_poly(3, 3, &mut rng);
        let f2 = rand_poly(3, 2, &mut rng);

        // SumCheckRelationの生成
        let T1 = Fr::rand(&mut rng);
        let u1 = vec![Fr::rand(&mut rng); 3];
        let x1 = vec![Fr::rand(&mut rng)];
        let w1 = vec![Fr::rand(&mut rng); 3];
        let sc1 = SumCheckRelation::new(T1, u1, x1, w1, g1, f1);

        let T2 = Fr::rand(&mut rng);
        let u2 = vec![Fr::rand(&mut rng); 3];
        let x2 = vec![Fr::rand(&mut rng)];
        let w2 = vec![Fr::rand(&mut rng); 3];
        let sc2 = SumCheckRelation::new(T2, u2, x2, w2, g2, f2);

        // 2つのSumCheckRelationを畳み込む
        let folded_sc = SumFold::<Fr, G1Projective, DensePolynomial<Fr>, SparsePolynomial<Fr, SparseTerm>>::fold_two_sc(
            sc1,
            sc2,
        );

        // Poseidon設定の取得
        let poseidon_config = poseidon_test_config::<Fr>();
        
        // 畳み込んだ多項式でSumCheckを実行
        type SC = SumCheck<Fr, G1Projective, DensePolynomial<Fr>, SparsePolynomial<Fr, SparseTerm>>;
        let proof = SC::prove(&poseidon_config, folded_sc.g.clone());

        // SumCheckの検証を実行
        let verification_result = SC::verify(&poseidon_config, proof);
        assert!(verification_result, "Folded SumCheckRelation failed verification");
    }
}