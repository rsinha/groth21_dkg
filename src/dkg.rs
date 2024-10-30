use rand::Rng;
use std::collections::BTreeMap;

use ark_ec::*;
use ark_ff::*;
use ark_std::marker::PhantomData;
use ark_std::ops::*;

use crate::nizk;
use crate::pke::*;
use crate::sss::*;
use crate::lagrange::*;
use crate::nizk::*;

/// message sent by a node during the setup or rekey protocol
pub struct DKGMessage<G: CurveGroup> {
    pub share_id: ShareId<G>,
    pub ctxt: ElGamalChunkedCiphertextMulti<G>,
    pub commitment: Vec<G::Affine>,
    pub proof: Proof<G>,
}

/// the id this node will use for identifying shares
pub type NodeId = u64;

/// the id this node will use for identifying shares
pub type ShareId<G> = <<G as CurveGroup>::Config as CurveConfig>::ScalarField;

/// field element encoding the BLS secret key (or its share)
pub type BlsSecretKey<G> = <<G as CurveGroup>::Config as CurveConfig>::ScalarField;

/// group element encoding the BLS public key
pub type BlsPublicKey<G> = <G as CurveGroup>::Affine;

#[derive(Clone)]
pub struct AddrBookEntry<G: CurveGroup> {
    pub node_id: NodeId, // unique id for the node
    pub elgamal_public_key: ElGamalPublicKey<G>, // ElGamal public key
    pub bls_public_keys: BTreeMap<ShareId<G>, Option<BlsPublicKey<G>>>, // BLS public keys of all shares held by the node
}

pub type AddrBook<G> = Vec<AddrBookEntry<G>>;

#[derive(Clone)]
pub struct NodeState<G: CurveGroup> {
    pub node_id: NodeId,
    pub elgamal_secret_key: ElGamalSecretKey<G>,
    pub bls_secret_keys: BTreeMap<ShareId<G>, Option<BlsSecretKey<G>>>,
}

// only used for simulation purposes, real protocol does not have this!
pub type NetworkState<G> = Vec<NodeState<G>>;

pub struct GrothDKG<G: CurveGroup> {
    _engine: PhantomData<G>,
    state: NetworkState<G>,
    addr_book: AddrBook<G>,
    candidate_addr_book: AddrBook<G>,
}

impl<G> GrothDKG<G>
    where G: CurveGroup
{
    pub fn init() -> Self {
        GrothDKG {
            _engine: PhantomData,
            state: NetworkState::<G>::new(),
            addr_book: AddrBook::<G>::new(),
            candidate_addr_book: AddrBook::<G>::new(),
        }
    }

    fn extract_share_claims_from_addr_book(addr_book: &AddrBook<G>) -> Vec<(ShareId<G>, ElGamalPublicKey<G>)> {
        addr_book.iter().map(|entry| {
            entry.bls_public_keys.iter().map(|(share_id, _)| {
                (share_id.clone(), entry.elgamal_public_key.clone())
            }).collect::<Vec<_>>()
        }).flatten().collect::<Vec<_>>()
    }

    pub fn setup<R: Rng>(&mut self, rng: &mut R) {
        let n = self.candidate_addr_book.len();
        let t = n / 2 + 1;
        
        let claims: Vec<(ShareId<G>, ElGamalPublicKey<G>)> = Self::extract_share_claims_from_addr_book(&self.candidate_addr_book);

        // all share ids as field elements
        let share_ids = claims.iter().map(|(id, _)| id.clone()).collect::<Vec<ShareId<G>>>();
        // all public keys, arranged by the above ids
        let pks = claims.iter().map(|(_, pk)| pk.clone()).collect::<Vec<ElGamalPublicKey<G>>>();

        // build reverse mapping from share_id to node_id
        let share_id_to_node_id: BTreeMap<ShareId<G>, NodeId> = self.candidate_addr_book.iter().map(|entry| {
            entry.bls_public_keys.iter().map(|(share_id, _)| {
                (share_id.clone(), entry.node_id)
            }).collect::<Vec<_>>()
        }).flatten().collect();

        let mut dkg_messages = Vec::new();
        // let's simulate the work of all dealers
        for share_id in share_ids.iter() {
            // each dealer will choose its own entropy
            let entropy = BlsSecretKey::<G>::rand(rng);
            // ... and will secret-share it with the other nodes
            let (shares, poly) = share(entropy, t, &share_ids);

            // arrange share values (the y-coordinate) by the node ids above
            let shares_y = share_ids.iter().map(|id| {
                shares.iter().find(|share| share.0 == *id).unwrap().1
            }).collect::<Vec<_>>();

            // all receivers share the randomness, so let's establish that first
            let rs = (0..32).map(|_| G::ScalarField::rand(rng)).collect::<Vec<G::ScalarField>>();

            let ctxt = ElGamal::<G>::chunked_encrypt_multi_receiver(&pks, &shares_y, &rs);

            let combined_ctxt = ElGamal::<G>::combine_chunked_ciphertext(&ctxt);
            let combined_rand = rs
                .iter()
                .enumerate()
                .fold(
                    G::ScalarField::zero(),
                    |acc, (i, &r)| acc + r * G::ScalarField::from(256u64).pow([i as u64])
                );
            let poly_commitment = nizk::feldman_commitment::<G>(&poly);

            let statement: nizk::Statement<G> = nizk::Statement {
                ids: share_ids.clone(),
                public_keys: pks.clone(),
                polynomial_commitment: poly_commitment.clone(),
                ciphertext_values: combined_ctxt.c2,
                ciphertext_rand: combined_ctxt.c1,
            };

            let witness: nizk::Witness<G> = nizk::Witness {
                rand: combined_rand,
                share_values: shares_y.clone(),
            };

            // let's create the DKG message that encrypts all shares under the node ids above
            dkg_messages.push(
                DKGMessage {
                    ctxt: ctxt,
                    share_id: share_id.clone(),
                    proof: prove(&witness, &statement, rng),
                    commitment: poly_commitment.clone(),
                }
            );
        }

        let valid_dkg_messages: Vec<&DKGMessage<G>> = dkg_messages
            .iter()
            .filter(|msg| {
                // let share_id = msg.share_id;
                // //iterate over all entries to find a matching share id in the hashmap
                // let Some(entry) = self.candidate_addr_book.iter().find(|entry| entry.bls_public_keys.contains_key(&share_id));
                // let share_public_key = entry.bls_public_keys.get(&share_id).unwrap();

                Self::verify_dkg_message(msg, &pks, &share_ids, &None)
            })
            .collect();

        // let's compute the next address book and network state
        let mut genesis_network_state = NetworkState::<G>::new();
        let mut genesis_addr_book = AddrBook::<G>::new();
        let cache = ElGamal::<G>::generate_cache();

        for (receiver_index, receiver_share_id) in share_ids.iter().enumerate() {

            let node_id = share_id_to_node_id.get(receiver_share_id).unwrap();
            // find receiver state in the network state data structure
            let receiver_state = self.state
                .iter()
                .find(|state_entry| state_entry.node_id == *node_id)
                .unwrap();

            let new_bls_secret_key = Self::process_setup_messages(
                receiver_index as u64,
                &receiver_state.elgamal_secret_key,
                &valid_dkg_messages,
                &cache
            );
            
            let new_bls_public_key = Self::compute_share_public_key_setup(&valid_dkg_messages, receiver_share_id);
            assert!(new_bls_public_key == G::generator().mul(&new_bls_secret_key).into_affine());

            // does genesis_network_state contain the node_id?
            if genesis_network_state.iter().find(|state| state.node_id == *node_id).is_none() {
                let new_state = NodeState {
                    node_id: *node_id,
                    elgamal_secret_key: receiver_state.elgamal_secret_key.clone(),
                    bls_secret_keys: BTreeMap::new(),
                };

                genesis_network_state.push(new_state);
            }

            // add bls secret key to the node's state
            genesis_network_state.iter_mut().find(|state| state.node_id == *node_id).unwrap().bls_secret_keys.insert(*receiver_share_id, Some(new_bls_secret_key));

            // does genesis_addr_book contain the node_id?
            if genesis_addr_book.iter().find(|entry| entry.node_id == *node_id).is_none() {
                let new_addr_book_entry = AddrBookEntry {
                    node_id: *node_id,
                    elgamal_public_key: self.candidate_addr_book.iter().find(|entry| entry.node_id == *node_id).unwrap().elgamal_public_key,
                    bls_public_keys: BTreeMap::new(),
                };

                genesis_addr_book.push(new_addr_book_entry);
            }
            // add bls public key to the node's address book entry
            genesis_addr_book.iter_mut().find(|entry| entry.node_id == *node_id).unwrap().bls_public_keys.insert(*receiver_share_id, Some(new_bls_public_key));
        }

        self.state = genesis_network_state;
        self.addr_book = genesis_addr_book.clone();
        self.candidate_addr_book = genesis_addr_book.clone();

    }

    fn process_setup_messages(
        receiver_index: u64,
        elgamal_secret_key: &ElGamalSecretKey<G>,
        messages: &Vec<&DKGMessage<G>>,
        cache: &ElGamalCache<G>
    ) -> BlsSecretKey<G> {

        messages.iter().fold(BlsSecretKey::<G>::zero(), |acc, message| {
            let share_y = ElGamal::<G>::chunked_decrypt_multi_receiver(
                receiver_index,
                &elgamal_secret_key,
                &message.ctxt,
                cache
            );
            acc + share_y
        })
    }

    // creates a new node in the address book (and state) with the ElGamal key that the node chose
    pub fn add_node(&mut self, elgamal_secret_key: &ElGamalSecretKey<G>, num_shares: u64) {
        let elgamal_public_key = G::generator().mul(elgamal_secret_key).into_affine();

        // let's give this node a brand new id, which is 1 more than the maximum id in the address book
        let max_existing_id = self.candidate_addr_book
            .iter()
            .map(|entry| entry.node_id)
            .max()
            .unwrap_or(0);

        let node_id = max_existing_id + 1;

        // grab all shares from the address book
        let shares = self.candidate_addr_book.iter().map(|entry| {
            entry.bls_public_keys.iter().map(|(share_id, _)| { share_id.clone() }).collect::<Vec<_>>()
        }).flatten().collect::<Vec<_>>();

        // find the max share
        let first_share = *shares.iter().max().unwrap_or(&ShareId::<G>::zero()) + ShareId::<G>::one();
        let share_ids = (0..num_shares).map(|i| first_share + ShareId::<G>::from(i as u64)).collect::<Vec<ShareId<G>>>();
        // create a btree map with all share ids and None as the value
        let bls_public_keys = share_ids.iter().map(|id| { (id.clone(), None) }).collect::<BTreeMap<ShareId<G>, Option<BlsPublicKey<G>>>>();
        let bls_secret_keys = share_ids.iter().map(|id| { (id.clone(), None) }).collect::<BTreeMap<ShareId<G>, Option<BlsSecretKey<G>>>>();

        // we only touch the candidate addr_book
        self.candidate_addr_book.push(AddrBookEntry {
            node_id: node_id,
            elgamal_public_key: elgamal_public_key,
            bls_public_keys: bls_public_keys,
        });
        
        self.state.push(NodeState {
            node_id: node_id,
            elgamal_secret_key: elgamal_secret_key.clone(),
            bls_secret_keys: bls_secret_keys,
        });
    }

    pub fn remove_node(&mut self, node_id: &NodeId) {
        // collect all entries that are not the node_id to be removed
        let all_but_nodeid_addr_book = self.candidate_addr_book
            .iter()
            .filter(|entry| entry.node_id != *node_id)
            .cloned()
            .collect::<AddrBook<G>>();

        // we only touch the candidate addr_book, not the active addr_book
        self.candidate_addr_book = all_but_nodeid_addr_book;

        let all_but_nodeid_state = self.state
            .iter()
            .filter(|state| state.node_id != *node_id)
            .cloned()
            .collect::<NetworkState<G>>();

        self.state = all_but_nodeid_state;
    }

    pub fn rekey<R: Rng>(&mut self, rng: &mut R) {

        let next_n = self.candidate_addr_book.len();
        let next_t = next_n / 2 + 1;
        
        let claims: Vec<(ShareId<G>, ElGamalPublicKey<G>)> = Self::extract_share_claims_from_addr_book(&self.candidate_addr_book);

        // all share ids as field elements
        let next_ids = claims.iter().map(|(id, _)| id.clone()).collect::<Vec<ShareId<G>>>();
        // all public keys, arranged by the above ids
        let next_pks = claims.iter().map(|(_, pk)| pk.clone()).collect::<Vec<ElGamalPublicKey<G>>>();

        // build reverse mapping from share_id to node_id
        let share_id_to_node_id: BTreeMap<ShareId<G>, NodeId> = self.candidate_addr_book.iter().map(|entry| {
            entry.bls_public_keys.iter().map(|(share_id, _)| {
                (share_id.clone(), entry.node_id)
            }).collect::<Vec<_>>()
        }).flatten().collect();

        let mut dkg_messages = Vec::new();

        // let's simulate the work of all dealers
        for dealer_entry in self.addr_book.iter() {

            // find the dealer's state in the network state data structure
            let dealer_state = self.state
                .iter()
                .find(|state_entry| state_entry.node_id == dealer_entry.node_id)
                .unwrap();

            // iterate for each share id owned by this dealer
            for (share_id, bls_secret) in dealer_state.bls_secret_keys.iter() {

                let bls_secret = bls_secret.unwrap();
                // ... and will secret-share it with the other nodes
                let (shares, poly) = share(bls_secret, next_t, &next_ids);

                // arrange share values (the y-coordinate) by the node ids above
                let shares_y = next_ids.iter().map(|id| {
                    shares.iter().find(|share| share.0 == *id).unwrap().1
                }).collect::<Vec<_>>();

                // all receivers share the randomness, so let's establish that first
                let rs = (0..32).map(|_| G::ScalarField::rand(rng)).collect::<Vec<G::ScalarField>>();

                let ctxt = ElGamal::<G>::chunked_encrypt_multi_receiver(&next_pks, &shares_y, &rs);

                let combined_ctxt = ElGamal::<G>::combine_chunked_ciphertext(&ctxt);
                let combined_rand = rs
                    .iter()
                    .enumerate()
                    .fold(
                        G::ScalarField::zero(),
                        |acc, (i, &r)| acc + r * G::ScalarField::from(256u64).pow([i as u64])
                    );
                let poly_commitment = nizk::feldman_commitment::<G>(&poly);

                let statement: nizk::Statement<G> = nizk::Statement {
                    ids: next_ids.clone(),
                    public_keys: next_pks.clone(),
                    polynomial_commitment: poly_commitment.clone(),
                    ciphertext_values: combined_ctxt.c2,
                    ciphertext_rand: combined_ctxt.c1,
                };

                let witness: nizk::Witness<G> = nizk::Witness {
                    rand: combined_rand,
                    share_values: shares_y.clone(),
                };

                // let's create the DKG message that encrypts all shares under the node ids above
                dkg_messages.push(
                    DKGMessage {
                        ctxt: ctxt,
                        share_id: share_id.clone(),
                        proof: prove(&witness, &statement, rng),
                        commitment: poly_commitment.clone(),
                    }
                );
            }

        }

        let ctxt_size_by_each_node = 
            dkg_messages[0].ctxt.c1.len() + 
            dkg_messages[0].ctxt.c2.len() * dkg_messages[0].ctxt.c2[0].len();
        let each_node_output =  ((ctxt_size_by_each_node * 48) as f64) / ((1024 * 1024) as f64);
        println!("communication requirement per node: {} MB", each_node_output);
        println!("communication requirement total: {} MB", each_node_output * next_n as f64);
        println!("dkg messages: {:?}", dkg_messages.len());

        let cache = ElGamal::<G>::generate_cache();

        let valid_dkg_messages: Vec<&DKGMessage<G>> = dkg_messages
            .iter()
            .filter(|msg| {
                //iterate over all entries to find a matching share id in the hashmap
                let entry = self.candidate_addr_book.iter().find(|entry| entry.bls_public_keys.contains_key(&msg.share_id)).unwrap();
                let share_public_key = entry.bls_public_keys.get(&msg.share_id).unwrap();

                Self::verify_dkg_message(msg, &next_pks, &next_ids, &share_public_key)
            })
            .collect();
        println!("valid dkg messages: {:?}", valid_dkg_messages.len());

        // let's compute the output address book and network state
        let mut next_network_state = NetworkState::<G>::new();
        let mut next_addr_book = AddrBook::<G>::new();

        for (receiver_index, receiver_share_id) in next_ids.iter().enumerate() {

            let node_id = share_id_to_node_id.get(receiver_share_id).unwrap();
            // find receiver state in the network state data structure
            let receiver_state = self.state
                .iter()
                .find(|state_entry| state_entry.node_id == *node_id)
                .unwrap();

            let rekey_compute_time = std::time::Instant::now();
            let new_bls_secret_key = Self::compute_share_secret_key(
                receiver_index as u64,
                &receiver_state.elgamal_secret_key,
                &valid_dkg_messages,
                &cache
            );
            
            let new_bls_public_key = Self::compute_share_public_key_rekey(&valid_dkg_messages, receiver_share_id);
            assert!(new_bls_public_key == G::generator().mul(&new_bls_secret_key).into_affine());

            println!("computation requirement per node: {:?}", rekey_compute_time.elapsed());

            // does genesis_network_state contain the node_id?
            if next_network_state.iter().find(|state| state.node_id == *node_id).is_none() {
                let new_state = NodeState {
                    node_id: *node_id,
                    elgamal_secret_key: receiver_state.elgamal_secret_key.clone(),
                    bls_secret_keys: BTreeMap::new(),
                };

                next_network_state.push(new_state);
            }

            // add bls secret key to the node's state
            next_network_state.iter_mut().find(|state| state.node_id == *node_id).unwrap().bls_secret_keys.insert(*receiver_share_id, Some(new_bls_secret_key));

            // does genesis_addr_book contain the node_id?
            if next_addr_book.iter().find(|entry| entry.node_id == *node_id).is_none() {
                let new_addr_book_entry = AddrBookEntry {
                    node_id: *node_id,
                    elgamal_public_key: self.candidate_addr_book.iter().find(|entry| entry.node_id == *node_id).unwrap().elgamal_public_key,
                    bls_public_keys: BTreeMap::new(),
                };

                next_addr_book.push(new_addr_book_entry);
            }
            // add bls public key to the node's address book entry
            next_addr_book.iter_mut().find(|entry| entry.node_id == *node_id).unwrap().bls_public_keys.insert(*receiver_share_id, Some(new_bls_public_key));
        }

        self.state = next_network_state;

        // let's set candidate to be same as active
        self.addr_book = next_addr_book.clone();
        self.candidate_addr_book = next_addr_book.clone();
    }

    fn verify_dkg_message(
        message: &DKGMessage<G>,
        pks: &Vec<ElGamalPublicKey<G>>,
        ids: &Vec<ShareId<G>>,
        share_public_key: &Option<BlsPublicKey<G>>
    ) -> bool {
        // does the polynomial commitment match up with the previous public key?
        if let Some(expected_commitment) = *share_public_key {
            let broadcasted_commitment = message.commitment[0];
            if broadcasted_commitment != expected_commitment {
                return false;
            }
        }

        // verify the NIZK proof
        let combined_ctxt = ElGamal::<G>::combine_chunked_ciphertext(&message.ctxt);
        let statement: nizk::Statement<G> = nizk::Statement {
            ids: ids.clone(),
            public_keys: pks.clone(),
            polynomial_commitment: message.commitment.clone(),
            ciphertext_values: combined_ctxt.c2,
            ciphertext_rand: combined_ctxt.c1,
        };
        if !verify(&statement, &message.proof) {
            return false;
        }

        return true;
    }

    fn compute_share_secret_key(
        receiver_index: u64,
        elgamal_secret_key: &ElGamalSecretKey<G>,
        dkg_messages: &Vec<&DKGMessage<G>>,
        cache: &ElGamalCache<G>,
    ) -> BlsSecretKey<G> {

        let mut incoming_shares: Vec<(ShareId<G>, ElGamalSecretKey<G>)> = Vec::new();

        // let's simulate the work of a receiver, which has to decrypt each dealer's message
        for dkg_message in dkg_messages.iter() {
            let share_y = ElGamal::<G>::chunked_decrypt_multi_receiver(
                receiver_index,
                elgamal_secret_key,
                &dkg_message.ctxt,
                cache
            );

            incoming_shares.push((dkg_message.share_id.clone(), share_y));
        }

        recover::<BlsSecretKey<G>>(&incoming_shares)
    }

    pub fn compute_share_public_key_setup(
        dkg_messages: &Vec<&DKGMessage<G>>,
        share_id: &ShareId<G>
    ) -> BlsPublicKey<G> {

        let mut dealt_share_pubkeys = Vec::new();

        for msg in dkg_messages.iter() {
            // compute powers of share_id
            let xs = (0..msg.commitment.len()).map(|i| share_id.pow([i as u64])).collect::<Vec<ShareId<G>>>();
            let share_of_share_pubkey = msg.commitment.iter().zip(xs.iter()).fold(G::zero(), |acc, (&a_i, &x_i)| { acc + a_i.mul(x_i) });
            dealt_share_pubkeys.push(share_of_share_pubkey);
        }

        let public_key = dealt_share_pubkeys.iter().fold(G::zero(), |acc, y_i| { acc + y_i });

        return public_key.into_affine();
    }

    pub fn compute_share_public_key_rekey(
        dkg_messages: &Vec<&DKGMessage<G>>,
        share_id: &ShareId<G>
    ) -> BlsPublicKey<G> {

        let mut dealt_share_pubkeys = Vec::new();
        let mut dealer_ids = Vec::new();

        for msg in dkg_messages.iter() {
            // compute powers of share_id
            let xs = (0..msg.commitment.len()).map(|i| share_id.pow([i as u64])).collect::<Vec<ShareId<G>>>();

            let share_of_share_pubkey = msg.commitment.iter().zip(xs.iter()).fold(G::zero(), |acc, (&a_i, &x_i)| { acc + a_i.mul(x_i) });

            dealt_share_pubkeys.push(share_of_share_pubkey);
            dealer_ids.push(msg.share_id);
        }

        let λs: Vec<ShareId<G>> = (0..dealer_ids.len()).map(|i| { lagrange_coefficient(&dealer_ids, i, ShareId::<G>::zero()) }).collect();

        let public_key = λs.iter().zip(dealt_share_pubkeys.iter())
            .fold(G::zero(), |acc, (&λ_i, &y_i)| { acc + y_i.mul(λ_i) });

        return public_key.into_affine();
    }

    pub fn compute_ledger_id(&self) -> BlsPublicKey<G> {

        let commitments = self.addr_book.iter().map(|entry| {
            entry.bls_public_keys.iter().map(|(share_id, bls_public_key)| {
                (share_id.clone(), bls_public_key.clone())
            }).collect::<Vec<_>>()
        }).flatten().collect::<Vec<_>>();

        // grab ids from commitments
        let ids = commitments.iter().map(|(id, _)| id.clone()).collect::<Vec<ShareId<G>>>();
        // grab public keys from commitments
        let pks = commitments.iter().map(|(_, pk)| pk.unwrap().clone()).collect::<Vec<BlsPublicKey<G>>>();

        let λs: Vec<ShareId<G>> = (0..ids.len()).map(|i| { lagrange_coefficient(&ids, i, ShareId::<G>::zero()) }).collect();

        let public_key = λs.iter().zip(pks.iter())
            .fold(G::zero(), |acc, (&λ_i, &pk_i)| { acc + pk_i.mul(λ_i) });

        return public_key.into_affine();
    }

}


#[cfg(test)]
mod tests {
    use crate::sss;
    use ark_std::test_rng;
    use super::*;

    type G = ark_bls12_381::G1Projective;

    fn simulate_bls_secret_recovery(network_state: &NetworkState<G>) -> BlsSecretKey<G> {

        //collect all shares from state
        let shares = network_state.iter().map(|entry| {
            entry.bls_secret_keys.iter().map(|(share_id, bls_secret_share)| {
                (share_id.clone(), bls_secret_share.unwrap().clone())
            }).collect::<Vec<_>>()
        }).flatten().collect::<Vec<_>>();

        sss::recover::<BlsSecretKey<G>>(&shares)
    }

    #[test]
    fn test_dkg_large() {
        let rng = &mut test_rng();
        let network_size = 12;

        let mut network = GrothDKG::<G>::init();

        // let's add network_size number of nodes
        for _i in 0..network_size {
            let sk = ElGamalSecretKey::<G>::rand(rng);
            network.add_node(&sk, 1);
        }

        // run the genesis protocol
        network.setup(rng);

        let ledger_id_secret = simulate_bls_secret_recovery(&network.state);
        let ledger_id = network.compute_ledger_id();

        // let's do a rekey with the same set of nodes
        network.rekey(rng);

        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));
        assert_eq!(ledger_id, network.compute_ledger_id());
    }

    #[test]
    fn test_dkg_remove() {
        let rng = &mut test_rng();
        let initial_network_size = 5;

        let mut network = GrothDKG::<G>::init();

        for _i in 0..initial_network_size {
            network.add_node(&ElGamalSecretKey::<G>::rand(rng), 3);
        }

        network.setup(rng);
        let ledger_id = network.compute_ledger_id();
        let ledger_id_secret = simulate_bls_secret_recovery(&network.state);

        // let's first do a rekey with the same set of nodes...because why not!
        network.rekey(rng);
        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));
        assert_eq!(ledger_id, network.compute_ledger_id());

        // let's remove a node (say node 0) and rekey
        network.remove_node(&0u64);

        network.rekey(rng);
        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));
        assert_eq!(ledger_id, network.compute_ledger_id());

        // let's add two nodes and rekey
        network.add_node(&ElGamalSecretKey::<G>::rand(rng), 2);
        network.add_node(&ElGamalSecretKey::<G>::rand(rng), 1);

        network.rekey(rng);
        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));
        assert_eq!(ledger_id, network.compute_ledger_id());

    }

    #[test]
    fn test_dkg_add() {

        let rng = &mut test_rng();
        let initial_network_size = 5;

        let mut network = GrothDKG::<G>::init();

        for _i in 0..initial_network_size {
            network.add_node(&ElGamalSecretKey::<G>::rand(rng), 3);
        }

        network.setup(rng);
        let ledger_id = network.compute_ledger_id();
        let ledger_id_secret = simulate_bls_secret_recovery(&network.state);

        // let's add two nodes and rekey
        for _i in 0..2 {
            network.add_node(&ElGamalSecretKey::<G>::rand(rng), 2);
        }
        network.rekey(rng);
        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));
        assert_eq!(ledger_id, network.compute_ledger_id());

        // let's add three nodes and rekey
        for _i in 0..3 {
            network.add_node(&ElGamalSecretKey::<G>::rand(rng), 1);
        }
        network.rekey(rng);
        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));
        assert_eq!(ledger_id, network.compute_ledger_id());
    }
}
