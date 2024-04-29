use ark_ec::*;
use ark_ff::*;
use ark_std::marker::PhantomData;
use ark_std::ops::*;
use ark_serialize::*;

use rand::Rng;

pub struct ElGamal<G: CurveGroup> {
    _engine: PhantomData<G>,
}

pub struct ElGamalCiphertext<G: CurveGroup> {
    pub c1: G::Affine,
    pub c2: G::Affine,
}

pub struct ElGamalChunkedCiphertext<G: CurveGroup> {
    pub cs: Vec<ElGamalCiphertext<G>>,
}

pub struct ElGamalChunkedCiphertextMulti<G: CurveGroup> {
    /// contains the randomness for each chunk; all receivers share randomness
    pub c1: Vec<G::Affine>,
    /// contains ciphertexts for each receiver, indexed first by the receiver and then by the chunk
    pub c2: Vec<Vec<G::Affine>>,
}

pub type ElGamalPublicKey<G> = <G as CurveGroup>::Affine;
pub type ElGamalSecretKey<G> = <<G as CurveGroup>::Config as CurveConfig>::ScalarField;
pub type ElGamalMessage<G> = <<G as CurveGroup>::Config as CurveConfig>::ScalarField;

impl<G> ElGamal<G>
    where G: CurveGroup
{
    /// generates a keypair for the ElGamal cryptosystem
    pub fn keygen<R: Rng>(rng: &mut R) -> (ElGamalSecretKey<G>, ElGamalPublicKey<G>) {
        let sk = G::ScalarField::rand(rng);
        let generator = G::generator();
        let pk = generator.mul(&sk);
        (sk, pk.into_affine())
    }

    /// returns an ElGamal ciphertext of the input message using the input public key
    pub fn encrypt<R: Rng>(
        pk: &ElGamalPublicKey<G>,
        m: ElGamalMessage<G>,
        rng: &mut R
    ) -> ElGamalCiphertext<G> {
        let generator = G::generator();

        let r = G::ScalarField::rand(rng);
        let c1 = generator.mul(&r).into_affine();
        let c2 = pk.mul(&r).add(&generator.mul(&m)).into_affine();

        ElGamalCiphertext { c1, c2 }
    }

    /// creates a chunked encryption of a message using the input public key
    pub fn chunked_encrypt<R: Rng>(
        pk: &ElGamalPublicKey<G>,
        msg: &ElGamalMessage<G>,
        rng: &mut R
    ) -> ElGamalChunkedCiphertext<G> {
        let mut serialized_msg = Vec::new();
        msg.serialize_compressed(&mut serialized_msg).unwrap();

        let mut cs: Vec<ElGamalCiphertext<G>> = Vec::new();

        let generator = G::generator();
        for (_j, chunk) in serialized_msg.iter().enumerate() {
            let r_j = G::ScalarField::rand(rng);
            let m_j = G::ScalarField::from(*chunk);
            let c1_j = generator.mul(&r_j).into_affine();
            let c2_j = pk.mul(&r_j).add(&generator.mul(&m_j)).into_affine();

            cs.push(ElGamalCiphertext { c1: c1_j, c2: c2_j });
        }

        ElGamalChunkedCiphertext { cs }
    }

    /// decrypts a chunked ElGamal ciphertext using the input decryption key;
    /// currently returns an unrecoverable error, if decryption fails (TODO: error handling)
    pub fn chunked_decrypt(
        sk: &ElGamalSecretKey<G>,
        c: &ElGamalChunkedCiphertext<G>
    ) -> ElGamalMessage<G> {
        let generator = G::generator();

        let mut msg = G::ScalarField::zero();

        for (j, c_j) in c.cs.iter().enumerate() {
            let anti_mask_j = c_j.c1.mul(G::ScalarField::zero() - sk); // g^(-r_j  * sk)
            let m_j_commitment = c_j.c2.add(anti_mask_j); // M_j = c2_j * g^(-r_j * sk) = g ^ m_j
            let m_j = ElGamal::<G>::brute_force_decrypt(&generator, &m_j_commitment).unwrap();
            msg += G::ScalarField::from(256u64).pow([j as u64]) * m_j;
        }

        msg
    }

    /// encrypts a message for multiple receivers using the input public keys;
    /// all ciphertexts use the same randomness, which not only saves space,
    /// but also enables efficient NIZK proofs in other parts of the DKG
    pub fn chunked_encrypt_multi_receiver<R: Rng>(
        pks: &[ElGamalPublicKey<G>],
        msgs: &[ElGamalMessage<G>],
        rng: &mut R
    ) -> ElGamalChunkedCiphertextMulti<G> {

         // l denotes the number of chunks of the serialized message
        let l = 32;
        let g = G::generator();

        // all receivers share the randomness, so let's establish that first
        let rs = (0..l).map(|_| G::ScalarField::rand(rng)).collect::<Vec<G::ScalarField>>();
        let c1: Vec<G::Affine> = rs.iter().map(|r_j| g.mul(r_j).into_affine()).collect();

        let mut c2: Vec<Vec<G::Affine>> = Vec::new();
        for (i, pk_i) in pks.iter().enumerate() {

            let mut serialized_msg = Vec::new();
            msgs[i].serialize_compressed(&mut serialized_msg).unwrap();

            let mut cs: Vec<G::Affine> = Vec::new();
            for (j, chunk) in serialized_msg.iter().enumerate() {
                let r_j = rs[j];
                let m_j = G::ScalarField::from(*chunk);
                let c2_j = pk_i.mul(&r_j).add(&g.mul(&m_j)).into_affine();
    
                cs.push(c2_j);
            }

            c2.push(cs);
        }

        ElGamalChunkedCiphertextMulti { c1, c2 }
    }

    /// decrypts a chunked ElGamal multi-ciphertext using the input decryption key
    pub fn chunked_decrypt_multi_receiver(
        receiver_id: usize,
        sk: &ElGamalSecretKey<G>,
        c: &ElGamalChunkedCiphertextMulti<G>,
    ) -> ElGamalMessage<G> {
        let g = G::generator();
        let mut msg = G::ScalarField::zero();

        for (j, c_j) in c.c2[receiver_id].iter().enumerate() {
            let anti_mask_j = c.c1[j].mul(G::ScalarField::zero() - sk); // g^(-r_j  * sk)
            let m_j_commitment = c_j.add(anti_mask_j); // M_j = c2_j * g^(-r_j * sk) = g ^ m_j
            let m_j = ElGamal::<G>::brute_force_decrypt(&g, &m_j_commitment).unwrap();
            msg += G::ScalarField::from(256u64).pow([j as u64]) * m_j;
        }

        msg
    }

    /// recovers the message from the commitment by brute force;
    /// this method tries all possible messages and returns 
    /// the one that matches the commitment
    fn brute_force_decrypt(
        base: &G,
        commitment: &G
    ) -> Option<ElGamalMessage<G>> {
        for i in 0..256 {
            let candidate = base.mul(&G::ScalarField::from(i as u64));
            if candidate.into_affine() == commitment.into_affine() {
                return Some(G::ScalarField::from(i as u64));
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type G = ark_bls12_381::G1Projective;

    #[test]
    fn test_chunked_encrypt() {
        let mut rng = rand::thread_rng();

        let (sk, pk) = ElGamal::<G>::keygen(&mut rng);

        let msg = ElGamalMessage::<G>::rand(&mut rng);
        let ctxt = ElGamal::<G>::chunked_encrypt(&pk, &msg, &mut rng);
        
        assert_eq!(msg, ElGamal::<G>::chunked_decrypt(&sk, &ctxt));
    }

    #[test]
    fn test_chunked_encrypt_multi_receiver() {
        let mut rng = rand::thread_rng();

        let (sk0, pk0) = ElGamal::<G>::keygen(&mut rng);
        let (sk1, pk1) = ElGamal::<G>::keygen(&mut rng);

        let pks = vec![pk0, pk1];
        let msgs = vec![ElGamalMessage::<G>::rand(&mut rng), ElGamalMessage::<G>::rand(&mut rng)];
        let ctxt = ElGamal::<G>::chunked_encrypt_multi_receiver(&pks, &msgs, &mut rng);
        
        assert_eq!(msgs[0], ElGamal::<G>::chunked_decrypt_multi_receiver(0, &sk0, &ctxt));
        assert_eq!(msgs[1], ElGamal::<G>::chunked_decrypt_multi_receiver(1, &sk1, &ctxt));
    }
}