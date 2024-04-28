use rand::{Rng, SeedableRng};
use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, *};

/// computes the Lagrange coefficient for the i-th point amongst the x-coordinates `xs`;
/// The output coefficient is the result of evaluating the Lagrange polynomial at the point `x`.
fn lagrange_coefficient<F: PrimeField>(xs: &[F], i: usize, x: F) -> F {
    // source: https://en.wikipedia.org/wiki/Lagrange_polynomial

    // the ith point must be within the range of the x-coordinates
    assert!(i < xs.len(), "index out of bounds");
    //assert that the x-coordinates are distinct
    assert_eq!(
        xs.iter().collect::<std::collections::HashSet<_>>().len(),
        xs.len(),
        "x-coordinates must be distinct"
    );

    let xi = xs[i];
    let mut numerator = F::one();
    let mut denominator = F::one();
    for (j, xj) in xs.iter().enumerate() {
        if i != j {
            numerator *= x - xj;
            denominator *= xi - xj;
        }
    }
    numerator * denominator.inverse().unwrap()
}

/// outputs a random polynomial with a fixed point at x = 0
fn sample_random_polynomial_with_secret<F: PrimeField, R: Rng>(
    evaluation_at_0: F,
    degree: usize,
    rng: &mut R,
) -> DensePolynomial<F> {
    // A t degree polynomial is defined by t + 1 coefficients: a_0, a_1, ..., a_t
    // such that p(x) = a_0 + a_1 * x + a_2 * x^2 + ... + a_t * x^t

    let mut coefficients = Vec::new();

    coefficients.push(evaluation_at_0); // a_0 is the evaluation at 0
    for _ in 0..degree { //
        coefficients.push(F::rand(rng)); // a_i is random coefficient
    }
    
    DensePolynomial { coeffs: coefficients }
}

/// outputs a (t,n) Shamir secret sharing of the input secret, 
/// where t is the threshold and n is the number of shares.
/// Note: the threshold t indicates that any t shares can be combined
/// to recover the secret, and any subset of t-1 shares cannot.
/// The output shares are (x,y) coordinate pairs.
pub fn share<F: PrimeField>(
    secret: F,
    threshold: usize,
    num_shares: usize
) -> Vec<(F, F)> {
    // generate random x-coordinates
    let mut rng = rand_chacha::ChaCha8Rng::from_seed([0u8; 32]);

    let p = sample_random_polynomial_with_secret(
        secret, threshold - 1, &mut rng
    );

    // we skip over 0 because that's where the secret is embedded
    let xs = (1..(num_shares + 1)).map(|i| F::from(i as u64)).collect::<Vec<F>>();
    let ys = xs.iter().map(|x| p.evaluate(x)).collect::<Vec<F>>();

    // output is a vector of (x,y) coordinate pairs
    xs.iter().zip(ys.iter()).map(|(x, y)| (*x, *y)).collect()
}

/// recovers the secret given a subset of t shares,
/// where each share is a (x,y) coordinate pair.
/// Note that this will return a arbitrary value 
/// if the reconstruction threshold is not met
pub fn recover<F: PrimeField>(
    shares: &[(F, F)],
) -> F {
    let xs = shares.iter().map(|(x, _)| *x).collect::<Vec<F>>();
    let ys = shares.iter().map(|(_, y)| *y).collect::<Vec<F>>();

    let λs: Vec<F> = (0..xs.len()).map(|i| {
        // each lagrange coefficient is computed with respect to x = 0,
        // since that's where we are embedding the secret in our entire
        // construction. So the ith coefficient is w.r.t. xs[i].
        let λ_i = lagrange_coefficient(&xs, i, F::zero()); λ_i
    }).collect();

    // the reconstructed secret is a weighted sum of ys, 
    // with the lagrange coefficients as weights
    let secret = λs.iter().zip(ys.iter())
        .fold(F::zero(), |acc, (&λ_i, &y_i)| { acc + λ_i * y_i });

    secret
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_share_and_recover() {
        let secret = ark_bls12_381::Fr::from(42u64);
        let threshold = 3;
        let num_shares = 5;

        let shares = share(secret, threshold, num_shares);

        assert_eq!(secret, recover(&shares[..threshold]));
        assert_eq!(secret, recover(&shares[1..4]));
        assert_eq!(secret, recover(&shares[2..5]));
        assert_eq!(secret, recover(&shares[..]));
        assert_eq!(secret, recover(vec![shares[0], shares[2], shares[4]].as_slice()));
    }

}