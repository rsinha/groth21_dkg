use std::collections::HashMap;
use rand::Rng;

use ark_ec::*;
use ark_ff::*;
use ark_std::marker::PhantomData;

use crate::pke::*;
use crate::sss::*;

pub struct DKGMessage<G: CurveGroup> {
    pub ctxt: ElGamalChunkedCiphertextMulti<G>,
    pub dealer_id: u64,
}

pub type NodeId<G> = <<G as CurveGroup>::Config as CurveConfig>::ScalarField;

pub type BlsSecretKey<G> = <<G as CurveGroup>::Config as CurveConfig>::ScalarField;

#[derive(Clone)]
pub struct AddrBookEntry<G: CurveGroup> {
    pub id: u64, // unique id for the node
    pub pk: ElGamalPublicKey<G>, // ElGamal public key
    pub commitment: Option<G::Affine>, // commitment to the BLS key share
}

pub type AddrBook<G> = HashMap<u64, AddrBookEntry<G>>;

#[derive(Clone)]
pub struct NodeState<G: CurveGroup> {
    id: u64,
    bls_secret_key: Option<BlsSecretKey<G>>,
    elgamal_secret_key: ElGamalSecretKey<G>,
}

pub type NetworkState<G> = HashMap<u64, NodeState<G>>;

pub struct GrothDKG<G: CurveGroup> {
    _engine: PhantomData<G>,
}

impl<G> GrothDKG<G>
    where G: CurveGroup
{
    pub fn setup<R: Rng>(
        genesis_addr_book: &AddrBook<G>,
        prev_network_state: &NetworkState<G>,
        rng: &mut R,
    ) -> (AddrBook<G>, NetworkState<G>) {
        let n = genesis_addr_book.len();
        let t = n.div_ceil(2);
        
        let pks = (0..n)
            .map(|i| genesis_addr_book.get(&(i as u64)).unwrap().pk)
            .collect::<Vec<_>>();

        let mut messages = HashMap::new();
        // let's simulate the work of all dealers
        for (dealer_id, _dealer_entry) in genesis_addr_book.iter() {
            // each dealer will choose its own entropy
            let entropy = BlsSecretKey::<G>::rand(rng);
            // ... and will secret-share it with the other nodes
            let shares = share(entropy, t, n);
            let shares_y = shares.iter().map(|share| share.1).collect::<Vec<_>>();

            // let's create the DKG message
            messages.insert(*dealer_id, DKGMessage {
                ctxt: ElGamal::<G>::chunked_encrypt_multi_receiver(&pks, &shares_y, rng),
                dealer_id: *dealer_id,
            });
        }

        let mut next_network_state = NetworkState::<G>::new();
        let mut next_addr_book = AddrBook::<G>::new();

        for (receiver_id, receiver_entry) in genesis_addr_book.iter() {
            let new_receiver_state = Self::process_setup_messages(prev_network_state.get(&receiver_entry.id).unwrap(), &messages);
            let new_receiver_blskey = new_receiver_state.bls_secret_key.unwrap().clone();

            next_network_state.insert(*receiver_id, new_receiver_state);
            next_addr_book.insert(*receiver_id, AddrBookEntry {
                id: *receiver_id,
                pk: receiver_entry.pk,
                commitment: Some(G::generator().mul(new_receiver_blskey).into_affine()),
            });
        }

        (next_addr_book, next_network_state)

    }

    fn process_setup_messages(node_state: &NodeState<G>, messages: &HashMap<u64, DKGMessage<G>>) -> NodeState<G> {
        let mut my_bls_key = BlsSecretKey::<G>::zero();

        // let's simulate the work of a receiver
        for (_dealer_id, message) in messages.iter() {
            // each node will decrypt the message
            let share_y = ElGamal::<G>::chunked_decrypt_multi_receiver(
                node_state.id,
                &node_state.elgamal_secret_key,
                &message.ctxt,
            );

            my_bls_key += share_y;
        }

        NodeState {
            id: node_state.id,
            bls_secret_key: Some(my_bls_key),
            elgamal_secret_key: node_state.elgamal_secret_key,
        }
    }

    pub fn add_node<R: Rng>(
        prev_addr_book: &AddrBook<G>,
        prev_network_state: &NetworkState<G>,
        elgamal_secret_key: &ElGamalSecretKey<G>,
    ) -> (AddrBook<G>, NetworkState<G>) {
        let mut next_addr_book = prev_addr_book.clone();
        let mut next_network_state = prev_network_state.clone();

        next_addr_book.insert(
            prev_addr_book.len() as u64,
            AddrBookEntry {
                id: prev_addr_book.len() as u64,
                pk: G::generator().mul(elgamal_secret_key).into_affine(),
                commitment: None,
            },
        );

        next_network_state.insert(
            prev_addr_book.len() as u64,
            NodeState {
                id: prev_addr_book.len() as u64,
                bls_secret_key: None,
                elgamal_secret_key: elgamal_secret_key.clone(),
            },
        );

        (next_addr_book, next_network_state)
    }

    pub fn rekey<R: Rng>(
        prev_addr_book: &AddrBook<G>,
        prev_network_state: &NetworkState<G>,
        candidate_addr_book: &AddrBook<G>,
        rng: &mut R,
    ) -> (AddrBook<G>, NetworkState<G>) {

        let next_t = candidate_addr_book.len().div_ceil(2);
        let next_n = candidate_addr_book.len();

        let next_pks = (0..next_n)
            .map(|i| candidate_addr_book.get(&(i as u64)).unwrap().pk)
            .collect::<Vec<_>>();

        let mut messages = HashMap::new();

        // let's simulate the work of all dealers
        for (dealer_id, _dealer_entry) in prev_addr_book.iter() {
            // each dealer will choose its own entropy
            let dealer_bls_key = prev_network_state.get(dealer_id).unwrap().bls_secret_key.unwrap();
            // ... and will secret-share it with the other nodes
            let shares = share(dealer_bls_key, next_t, next_n);
            let shares_y = shares.iter().map(|share| share.1).collect::<Vec<_>>();

            // let's create the DKG message
            messages.insert(*dealer_id, DKGMessage {
                ctxt: ElGamal::<G>::chunked_encrypt_multi_receiver(&next_pks, &shares_y, rng),
                dealer_id: *dealer_id,
            });
        }

        let mut next_network_state = NetworkState::<G>::new();
        let mut next_addr_book = AddrBook::<G>::new();

        for (receiver_id, receiver_entry) in candidate_addr_book.iter() {
            let new_receiver_state = Self::process_rekey_messages(prev_network_state.get(receiver_id).unwrap(), &messages);
            let new_receiver_blskey = new_receiver_state.bls_secret_key.unwrap().clone();

            next_network_state.insert(*receiver_id, new_receiver_state);
            next_addr_book.insert(*receiver_id, AddrBookEntry {
                id: *receiver_id,
                pk: receiver_entry.pk,
                commitment: Some(G::generator().mul(new_receiver_blskey).into_affine()),
            });
        }

        (next_addr_book, next_network_state)
    }


    fn process_rekey_messages(node_state: &NodeState<G>, messages: &HashMap<u64, DKGMessage<G>>) -> NodeState<G> {
        let mut incoming_shares: Vec<(NodeId<G>, ElGamalSecretKey<G>)> = Vec::new();

        // let's simulate the work of a receiver
        for (dealer_id, message) in messages.iter() {
            // each node will decrypt the message
            let share_y = ElGamal::<G>::chunked_decrypt_multi_receiver(
                node_state.id,
                &node_state.elgamal_secret_key,
                &message.ctxt,
            );

            incoming_shares.push((NodeId::<G>::from(*dealer_id), share_y));
        }

        let my_bls_key = recover::<BlsSecretKey<G>>(&incoming_shares);
        NodeState {
            id: node_state.id,
            bls_secret_key: Some(my_bls_key),
            elgamal_secret_key: node_state.elgamal_secret_key,
        }
    }

}

#[cfg(test)]
mod tests {
    use ark_std::test_rng;
    use ark_ec::*;
    use ark_std::ops::*;

    use super::*;
    type G = ark_bls12_381::G1Projective;

    #[test]
    fn test_dkg() {

        let rng = &mut test_rng();

        let n = 5;

        let mut genesis_network_state = NetworkState::<G>::new();
        let mut genesis_addr_book = AddrBook::<G>::new();

        for i in 0..n {
            let sk = ElGamalSecretKey::<G>::rand(rng);
            let pk = G::generator().mul(&sk).into_affine();

            genesis_addr_book.insert(i as u64, AddrBookEntry {
                id: i as u64,
                pk,
                commitment: None,
            });

            genesis_network_state.insert(i as u64, NodeState {
                id: i as u64,
                bls_secret_key: None,
                elgamal_secret_key: sk,
            });
        }

        let (addr_book_0, network_state_0) = GrothDKG::<G>::setup(&genesis_addr_book, &genesis_network_state, rng);

        let (addr_book_1, network_state_1) = GrothDKG::<G>::rekey(&addr_book_0, &network_state_0, &addr_book_0, rng);
    }
}