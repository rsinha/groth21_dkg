use ark_ec::*;
use ark_ff::*;
use ark_poly::univariate::DensePolynomial;
use rand::Rng;
use std::ops::*;

type ScalarField<G> = <<G as CurveGroup>::Config as CurveConfig>::ScalarField;

#[allow(non_snake_case)]
pub struct Statement<G: CurveGroup> {
    pub ids: Vec<ScalarField<G>>, // unique ids for the nodes receiving the shares
    pub public_keys: Vec<G::Affine>, // n public keys // (y1,...,yn) in the paper
    pub polynomial_commitment: Vec<G::Affine>, // t group elements // (A_0, ..., A_t-1) in the paper
    pub ciphertext_values: Vec<G::Affine>, // n ciphertexts // C1,...,Cn in the paper
    pub ciphertext_rand: G::Affine, // 1 group element // R in the paper
}

#[allow(non_snake_case)]
pub struct Witness<G: CurveGroup> {
    pub rand: ScalarField<G>, // r in the paper
    pub share_values: Vec<ScalarField<G>>, // n share values // (s1,...,sn) in the paper
}

#[allow(non_snake_case)]
pub struct Proof<G: CurveGroup> {
    pub F: G::Affine, // F in the paper
    pub A: G::Affine, // A in the paper
    pub Y: G::Affine, // Y in the paper
    pub z_r: ScalarField<G>, // z_r in the paper
    pub z_a: ScalarField<G>, // z_a in the paper
}

pub fn feldman_commitment<G: CurveGroup>(
    polynomial: &DensePolynomial<ScalarField<G>>
) -> Vec<G::Affine> {
    let generator = G::generator();

    polynomial.coeffs
        .iter()
        .map(|coeff| { generator.mul(coeff).into_affine() })
        .collect::<Vec<G::Affine>>()
}

#[allow(non_snake_case)]
pub fn prove<G: CurveGroup, R: Rng>(
    witness: &Witness<G>,
    statement: &Statement<G>,
    rng: &mut R
) -> Proof<G> {
    // compute x := RO(instance)
    let x = ScalarField::<G>::from(42u64); // obviously TODO

    // Generate random α, ρ ←$ Zp
    let alpha = ScalarField::<G>::rand(rng);
    let rho = ScalarField::<G>::rand(rng);

    // compute F = g^rho
    let F = G::generator().mul(&rho).into_affine();
    // compute A = g^alpha
    let A = G::generator().mul(&alpha).into_affine();

    // compute Y = Π_{i=1}^{n} (y_i)^x^i
    let inner = statement.public_keys
        .iter()
        .zip(statement.ids.iter())
        .fold(G::Affine::zero(), |acc, (y_i, &id_i)| {
        acc.add(y_i.mul(&x.pow(id_i.into_bigint())).into_affine()).into_affine()
    });
    let Y = inner.mul(rho).add(A).into_affine();

    // compute x' := RO(x, F, A, Y)
    let x_prime = ScalarField::<G>::from(86u64); // obviously TODO

    // compute z_r = x' * r + rho
    let z_r = x_prime * witness.rand + rho;

    // compute z_a = x' * Sigma_{i=1}^{n} (s_i)*x^i + alpha
    let z_a = alpha + x_prime * witness.share_values
        .iter()
        .zip(statement.ids.iter())
        .fold(ScalarField::<G>::zero(), |acc, (&s_i, &id_i)| {
            acc + s_i * x.pow(id_i.into_bigint())
        });

    Proof { F, A, Y, z_r, z_a }
}

#[allow(non_snake_case)]
pub fn verify<G: CurveGroup>(
    statement: &Statement<G>,
    proof: &Proof<G>
) -> bool {
    // compute x := RO(instance)
    let x = ScalarField::<G>::from(42u64); // obviously TODO
    // compute x' := RO(x, F, A, Y)
    let x_prime = ScalarField::<G>::from(86u64); // obviously TODO
    
    // check R ^ x' . F = g ^ z_r
    let lhs = statement.ciphertext_rand.mul(&x_prime).add(&proof.F).into_affine();
    let rhs = G::generator().mul(&proof.z_r).into_affine();
    if lhs != rhs { return false; }

    // compute product of feldman commitments raised to the power of x^i
    let inner = statement.polynomial_commitment
        .iter()
        .enumerate()
        .fold(G::Affine::zero(), |acc, (k, A_k)| {
            acc.add(
                A_k.mul(
                    statement.ids
                    .iter()
                    .fold(ScalarField::<G>::zero(), |acc, id_i| {
                        acc + id_i.pow([k as u64]) * x.pow(id_i.into_bigint())
                    })
                ).into_affine()
            ).into_affine()
        });
    let lhs = inner.mul(&x_prime).add(&proof.A).into_affine();
    let rhs = G::generator().mul(&proof.z_a).into_affine();
    if lhs != rhs { return false; }

    let inner = statement.ciphertext_values
        .iter()
        .zip(statement.ids.iter())
        .fold(G::Affine::zero(), |acc, (C_i, id_i)| {
            acc.add(C_i.mul(x.pow(id_i.into_bigint())).into_affine()).into_affine()
        });
    let lhs = inner.mul(&x_prime).add(&proof.Y).into_affine();
    let inner = statement.public_keys
        .iter()
        .zip(statement.ids.iter())
        .fold(G::Affine::zero(), |acc, (y_i, id_i)| {
            acc.add(y_i.mul(proof.z_r * x.pow(id_i.into_bigint())).into_affine()).into_affine()
        });
    let rhs = inner.add(G::generator().mul(proof.z_a)).into_affine();
    if lhs != rhs { return false; }

    return true;

}