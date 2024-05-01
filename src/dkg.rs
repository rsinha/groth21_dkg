use std::collections::HashMap;
use rand::Rng;

use ark_ec::*;
use ark_ff::*;
use ark_std::marker::PhantomData;

use crate::pke::*;
use crate::sss::*;

/// message sent by a node during the setup or rekey protocol
pub struct DKGMessage<G: CurveGroup> {
    pub dealer_id: NodeId<G>,
    pub ctxt: ElGamalChunkedCiphertextMulti<G>,
}

/// the id this node will use for identifying shares
pub type NodeId<G> = <<G as CurveGroup>::Config as CurveConfig>::ScalarField;

/// field element encoding the BLS secret key (or its share)
pub type BlsSecretKey<G> = <<G as CurveGroup>::Config as CurveConfig>::ScalarField;

/// group element encoding the BLS public key
pub type BlsPublicKey<G> = <G as CurveGroup>::Affine;

#[derive(Clone)]
pub struct AddrBookEntry<G: CurveGroup> {
    pub id: NodeId<G>, // unique id for the node
    pub pk: ElGamalPublicKey<G>, // ElGamal public key
    pub commitment: Option<BlsPublicKey<G>>, // commitment to the BLS key share
}

pub type AddrBook<G> = Vec<AddrBookEntry<G>>;

#[derive(Clone)]
pub struct NodeState<G: CurveGroup> {
    pub id: NodeId<G>,
    pub elgamal_secret_key: ElGamalSecretKey<G>,
    pub bls_secret_key: Option<BlsSecretKey<G>>,
}

pub type NetworkState<G> = Vec<NodeState<G>>;

pub struct GrothDKG<G: CurveGroup> {
    _engine: PhantomData<G>,
}

impl<G> GrothDKG<G>
    where G: CurveGroup
{
    pub fn setup<R: Rng>(
        pre_genesis_addr_book: &AddrBook<G>,
        pre_genesis_network_state: &NetworkState<G>,
        rng: &mut R,
    ) -> (AddrBook<G>, NetworkState<G>) {
        let n = pre_genesis_addr_book.len();
        let t = n / 2 + 1;
        println!("setting up with t: {}, n: {}", t, n);
        
        // all node ids as field elements
        let ids = pre_genesis_addr_book.iter().map(|entry| entry.id).collect::<Vec<NodeId<G>>>();
        // all public keys, arranged by the above ids
        let pks = pre_genesis_addr_book.iter().map(|entry| entry.pk).collect::<Vec<BlsPublicKey<G>>>();

        let mut dkg_messages = Vec::new();
        // let's simulate the work of all dealers
        for dealer_entry in pre_genesis_addr_book.iter() {
            // each dealer will choose its own entropy
            let entropy = BlsSecretKey::<G>::rand(rng);
            // ... and will secret-share it with the other nodes
            let shares = share(entropy, t, n);

            // arrange share values (the y-coordinate) by the node ids above
            let shares_y = ids.iter().map(|id| {
                shares.iter().find(|share| share.0 == *id).unwrap().1
            }).collect::<Vec<_>>();

            // let's create the DKG message that encrypts all shares under the node ids above
            dkg_messages.push(
                DKGMessage {
                    ctxt: ElGamal::<G>::chunked_encrypt_multi_receiver(&pks, &shares_y, rng),
                    dealer_id: dealer_entry.id.clone(),
                }
            );
        }

        // let's compute the output address book and network state
        let mut genesis_network_state = NetworkState::<G>::new();
        let mut genesis_addr_book = AddrBook::<G>::new();

        for (receiver_index, receiver_id) in ids.iter().enumerate() {
            // find receiver state in the network state data structure
            let receiver_state = pre_genesis_network_state
                .iter()
                .find(|state_entry| state_entry.id == *receiver_id)
                .unwrap();

            let new_bls_secret_key = Self::process_setup_messages(
                receiver_index as u64,
                &receiver_state.elgamal_secret_key,
                &dkg_messages
            );
            
            //TODO: need to derive this from the commitments in the DKG messages
            let new_bls_public_key = G::generator().mul(new_bls_secret_key).into_affine();

            let new_state = NodeState {
                id: *receiver_id,
                elgamal_secret_key: receiver_state.elgamal_secret_key.clone(),
                bls_secret_key: Some(new_bls_secret_key),
            };

            let new_addr_book_entry = AddrBookEntry {
                id: *receiver_id,
                pk: pre_genesis_addr_book.iter().find(|entry| entry.id == *receiver_id).unwrap().pk,
                commitment: Some(new_bls_public_key),
            };

            genesis_network_state.push(new_state);
            genesis_addr_book.push(new_addr_book_entry);
        }

        (genesis_addr_book, genesis_network_state)

    }

    fn process_setup_messages(
        receiver_index: u64,
        elgamal_secret_key: &ElGamalSecretKey<G>,
        messages: &Vec<DKGMessage<G>>
    ) -> BlsSecretKey<G> {
        // my bls key will be computed based on all the DKG messages I process
        let mut my_bls_key = BlsSecretKey::<G>::zero();

        // let's simulate the work of a receiver
        for message in messages.iter() {
            // each node will decrypt the message
            let share_y = ElGamal::<G>::chunked_decrypt_multi_receiver(
                receiver_index,
                &elgamal_secret_key,
                &message.ctxt,
            );

            my_bls_key += share_y;
        }

        my_bls_key
    }

    pub fn add_node(
        prev_addr_book: &AddrBook<G>,
        prev_network_state: &NetworkState<G>,
        elgamal_secret_key: &ElGamalSecretKey<G>,
    ) -> (AddrBook<G>, NetworkState<G>) {
        let mut next_addr_book = prev_addr_book.clone();
        let mut next_network_state = prev_network_state.clone();

        next_addr_book.push(AddrBookEntry {
            id: NodeId::<G>::from((prev_addr_book.len() + 1) as u64),
            pk: G::generator().mul(elgamal_secret_key).into_affine(),
            commitment: None,
        });
        
        next_network_state.push(NodeState {
            id: NodeId::<G>::from((prev_addr_book.len() + 1) as u64),
            elgamal_secret_key: elgamal_secret_key.clone(),
            bls_secret_key: None,
        });

        (next_addr_book, next_network_state)
    }

    pub fn rekey<R: Rng>(
        prev_addr_book: &AddrBook<G>,
        prev_network_state: &NetworkState<G>,
        candidate_addr_book: &AddrBook<G>,
        rng: &mut R,
    ) -> (AddrBook<G>, NetworkState<G>) {

        let next_n = candidate_addr_book.len();
        let next_t = next_n / 2 + 1;
        println!("rekeying with t: {}, n: {}", next_t, next_n);
        
        // all node ids as field elements
        let next_ids = candidate_addr_book.iter().map(|entry| entry.id).collect::<Vec<NodeId<G>>>();
        // all public keys, arranged by the above ids
        let next_pks = candidate_addr_book.iter().map(|entry| entry.pk).collect::<Vec<BlsPublicKey<G>>>();

        let mut dkg_messages = Vec::new();
        // let's simulate the work of all dealers
        for dealer_entry in prev_addr_book.iter() {

            // each dealer will secret-share its bls secret key
            let bls_secret = prev_network_state
                .iter()
                .find(|state| state.id == dealer_entry.id)
                .unwrap()
                .bls_secret_key
                .unwrap();

            // ... and will secret-share it with the other nodes
            let shares = share(bls_secret, next_t, next_n);

            // arrange share values (the y-coordinate) by the node ids above
            let shares_y = next_ids.iter().map(|id| {
                shares.iter().find(|share| share.0 == *id).unwrap().1
            }).collect::<Vec<_>>();

            // let's create the DKG message that encrypts all shares under the node ids above
            dkg_messages.push(
                DKGMessage {
                    ctxt: ElGamal::<G>::chunked_encrypt_multi_receiver(&next_pks, &shares_y, rng),
                    dealer_id: dealer_entry.id.clone(),
                }
            );
        }

        // let's compute the output address book and network state
        let mut next_network_state = NetworkState::<G>::new();
        let mut next_addr_book = AddrBook::<G>::new();

        for (receiver_index, receiver_id) in next_ids.iter().enumerate() {
            // find receiver state in the network state data structure
            let receiver_state = prev_network_state
                .iter()
                .find(|state_entry| state_entry.id == *receiver_id)
                .unwrap();

            let new_bls_secret_key = Self::process_rekey_messages(
                receiver_index as u64,
                &receiver_state.elgamal_secret_key,
                &dkg_messages
            );
            
            //TODO: need to derive this from the commitments in the DKG messages
            let new_bls_public_key = G::generator().mul(new_bls_secret_key).into_affine();

            let new_state = NodeState {
                id: *receiver_id,
                elgamal_secret_key: receiver_state.elgamal_secret_key.clone(),
                bls_secret_key: Some(new_bls_secret_key),
            };

            let new_addr_book_entry = AddrBookEntry {
                id: *receiver_id,
                pk: prev_addr_book.iter().find(|entry| entry.id == *receiver_id).unwrap().pk,
                commitment: Some(new_bls_public_key),
            };

            next_network_state.push(new_state);
            next_addr_book.push(new_addr_book_entry);
        }


        (next_addr_book, next_network_state)
    }


    fn process_rekey_messages(
        receiver_index: u64,
        elgamal_secret_key: &ElGamalSecretKey<G>,
        dkg_messages: &Vec<DKGMessage<G>>
    ) -> BlsSecretKey<G> {
        let mut incoming_shares: Vec<(NodeId<G>, ElGamalSecretKey<G>)> = Vec::new();

        // let's simulate the work of a receiver, which has to decrypt each dealer's message
        for dkg_message in dkg_messages.iter() {
            let share_y = ElGamal::<G>::chunked_decrypt_multi_receiver(
                receiver_index,
                elgamal_secret_key,
                &dkg_message.ctxt,
            );

            incoming_shares.push((dkg_message.dealer_id.clone(), share_y));
        }

        recover::<BlsSecretKey<G>>(&incoming_shares)
    }

}

#[cfg(test)]
mod tests {
    use crate::sss;
    use ark_std::test_rng;
    use super::*;

    type G = ark_bls12_381::G1Projective;

    fn simulate_bls_secret_recovery(network_state: &NetworkState<G>) -> BlsSecretKey<G> {
        let shares: Vec<(NodeId<G>, BlsSecretKey<G>)> = network_state.iter().map(|node_state| {
            (node_state.id.clone(), node_state.bls_secret_key.unwrap())
        }).collect();
        sss::recover::<BlsSecretKey<G>>(&shares)
    }

    #[test]
    fn test_dkg() {
        let rng = &mut test_rng();
        let n = 5;

        let mut network_state = NetworkState::<G>::new();
        let mut addr_book = AddrBook::<G>::new();

        for _i in 0..n {
            let sk = ElGamalSecretKey::<G>::rand(rng);
            
            (addr_book, network_state) = GrothDKG::<G>::add_node(
                &mut addr_book, 
                &mut network_state, 
                &sk
            );
        }

        let pre_genesis_addr_book = addr_book.clone();
        let pre_genesis_network_state = network_state.clone();

        let (genesis_addr_book, genesis_network_state) = GrothDKG::<G>::setup(
            &pre_genesis_addr_book,
            &pre_genesis_network_state,
            rng
        );

        let ledger_id = simulate_bls_secret_recovery(&genesis_network_state);
        let (mut addr_book, mut network_state) = (genesis_addr_book, genesis_network_state);
        let mut candidate_addr_book = addr_book.clone();

        (addr_book, network_state) = GrothDKG::<G>::rekey(
            &addr_book,
            &network_state,
            &candidate_addr_book,
            rng
        );

        assert_eq!(ledger_id, simulate_bls_secret_recovery(&network_state));

        // let sk = ElGamalSecretKey::<G>::rand(rng);
        // (candidate_addr_book, network_state) = GrothDKG::<G>::add_node(
        //     &addr_book, 
        //     &network_state, 
        //     &sk
        // );

        // (addr_book, network_state) = GrothDKG::<G>::rekey(
        //     &addr_book,
        //     &network_state,
        //     &candidate_addr_book,
        //     rng
        // );

        // assert_eq!(ledger_id, simulate_bls_secret_recovery(&network_state));
    }
}