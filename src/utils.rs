use ark_ec::*;
use ark_ff::*;
use ark_serialize::CanonicalSerialize;
use sha2::*;

pub fn serialize_field_element<F: PrimeField>(element: &F) -> Vec<u8> {
    let mut serialized = Vec::new();
    element.serialize_uncompressed(&mut serialized).unwrap();
    serialized
}

pub fn serialize_group_element<G: CurveGroup>(element: &G::Affine) -> Vec<u8> {
    let mut serialized = Vec::new();
    element.serialize_uncompressed(&mut serialized).unwrap();
    serialized
}

pub fn compute_sha256(input: &[u8]) -> [u8; 32] {
    let mut hasher = sha2::Sha256::new();
    hasher.update(input);
    hasher.finalize().into()
}