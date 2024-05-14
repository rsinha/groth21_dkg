use rand::Rng;

use ark_ec::*;
use ark_ff::*;
use ark_std::marker::PhantomData;

use crate::nizk;
use crate::pke::*;
use crate::sss::*;
use crate::nizk::*;

/// message sent by a node during the setup or rekey protocol
pub struct DKGMessage<G: CurveGroup> {
    pub dealer_id: NodeId<G>,
    pub ctxt: ElGamalChunkedCiphertextMulti<G>,
    pub commitment: Vec<G::Affine>,
    pub proof: Proof<G>,
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

    pub fn setup<R: Rng>(&mut self, rng: &mut R) {
        let n = self.candidate_addr_book.len();
        let t = n / 2 + 1;
        
        // all node ids as field elements
        let ids = self.candidate_addr_book.iter().map(|entry| entry.id).collect::<Vec<NodeId<G>>>();
        // all public keys, arranged by the above ids
        let pks = self.candidate_addr_book.iter().map(|entry| entry.pk).collect::<Vec<ElGamalPublicKey<G>>>();

        let mut dkg_messages = Vec::new();
        // let's simulate the work of all dealers
        for dealer_entry in self.candidate_addr_book.iter() {
            // each dealer will choose its own entropy
            let entropy = BlsSecretKey::<G>::rand(rng);
            // ... and will secret-share it with the other nodes
            let (shares, poly) = share(entropy, t, &ids);

            // arrange share values (the y-coordinate) by the node ids above
            let shares_y = ids.iter().map(|id| {
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
                ids: ids.clone(),
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
                    dealer_id: dealer_entry.id.clone(),
                    proof: prove(&witness, &statement, rng),
                    commitment: poly_commitment.clone(),
                }
            );
        }

        // let's compute the next address book and network state
        let mut genesis_network_state = NetworkState::<G>::new();
        let mut genesis_addr_book = AddrBook::<G>::new();
        let cache = ElGamal::<G>::generate_cache();

        for (receiver_index, receiver_id) in ids.iter().enumerate() {
            // find receiver state in the network state data structure
            let receiver_state = self.state
                .iter()
                .find(|state_entry| state_entry.id == *receiver_id)
                .unwrap();

            let new_bls_secret_key = Self::process_setup_messages(
                receiver_index as u64,
                &receiver_state.elgamal_secret_key,
                &dkg_messages,
                &pks,
                &ids,
                &cache
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
                pk: self.candidate_addr_book.iter().find(|entry| entry.id == *receiver_id).unwrap().pk,
                commitment: Some(new_bls_public_key),
            };

            genesis_network_state.push(new_state);
            genesis_addr_book.push(new_addr_book_entry);
        }

        self.state = genesis_network_state;
        self.addr_book = genesis_addr_book.clone();
        self.candidate_addr_book = genesis_addr_book.clone();

    }

    fn process_setup_messages(
        receiver_index: u64,
        elgamal_secret_key: &ElGamalSecretKey<G>,
        messages: &Vec<DKGMessage<G>>,
        pks: &Vec<ElGamalPublicKey<G>>,
        ids: &Vec<NodeId<G>>,
        cache: &ElGamalCache<G>
    ) -> BlsSecretKey<G> {
        //let's verify the messages first
        for message in messages.iter() {
            let combined_ctxt = ElGamal::<G>::combine_chunked_ciphertext(&message.ctxt);
            let statement: nizk::Statement<G> = nizk::Statement {
                ids: ids.clone(),
                public_keys: pks.clone(),
                polynomial_commitment: message.commitment.clone(),
                ciphertext_values: combined_ctxt.c2,
                ciphertext_rand: combined_ctxt.c1,
            };

            // for genesis, let's expect all parties to behave correctly
            // that said, this can be modified to just include the correct parties
            assert!(verify(&statement, &message.proof));
        }

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
    pub fn add_node(&mut self, elgamal_secret_key: &ElGamalSecretKey<G>) {
        let elgamal_public_key = G::generator().mul(elgamal_secret_key).into_affine();

        // let's give this node a brand new id, which is 1 more than the maximum id in the address book
        let max_existing_id = self.candidate_addr_book
            .iter()
            .map(|entry| entry.id)
            .max()
            .unwrap_or(NodeId::<G>::zero());

        let node_id = max_existing_id + NodeId::<G>::one();

        // we only touch the candidate addr_book
        self.candidate_addr_book.push(AddrBookEntry {
            id: node_id.clone(),
            pk: elgamal_public_key,
            commitment: None,
        });
        
        self.state.push(NodeState {
            id: node_id.clone(),
            elgamal_secret_key: elgamal_secret_key.clone(),
            bls_secret_key: None,
        });
    }

    pub fn remove_node(&mut self, node_id: &NodeId<G>) {
        // collect all entries that are not the node_id to be removed
        let all_but_nodeid_addr_book = self.candidate_addr_book
            .iter()
            .filter(|entry| entry.id != *node_id)
            .cloned()
            .collect::<AddrBook<G>>();

        // we only touch the candidate addr_book
        self.candidate_addr_book = all_but_nodeid_addr_book;
    }

    pub fn rekey<R: Rng>(&mut self, rng: &mut R) {

        let next_n = self.candidate_addr_book.len();
        let next_t = next_n / 2 + 1;
        
        // all node ids as field elements
        let next_ids = self.candidate_addr_book.iter().map(|entry| entry.id).collect::<Vec<NodeId<G>>>();
        // all public keys, arranged by the above ids
        let next_pks = self.candidate_addr_book.iter().map(|entry| entry.pk).collect::<Vec<ElGamalPublicKey<G>>>();

        let mut dkg_messages = Vec::new();

        // let's simulate the work of all dealers
        for dealer_entry in self.addr_book.iter() {

            // each dealer will secret-share its bls secret key
            let bls_secret = self.state
                .iter()
                .find(|state| state.id == dealer_entry.id)
                .unwrap()
                .bls_secret_key
                .unwrap();

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
                    dealer_id: dealer_entry.id.clone(),
                    proof: prove(&witness, &statement, rng),
                    commitment: poly_commitment.clone(),
                }
            );
        }

        let ctxt_size_by_each_node = 
            dkg_messages[0].ctxt.c1.len() + 
            dkg_messages[0].ctxt.c2.len() * dkg_messages[0].ctxt.c2[0].len();
        let each_node_output =  ((ctxt_size_by_each_node * 48) as f64) / ((1024 * 1024) as f64);
        println!("communication requirement per node: {} MB", each_node_output);
        println!("communication requirement total: {} MB", each_node_output * next_n as f64);

        // let's compute the output address book and network state
        let mut next_network_state = NetworkState::<G>::new();
        let mut next_addr_book = AddrBook::<G>::new();

        let cache = ElGamal::<G>::generate_cache();

        for (receiver_index, receiver_id) in next_ids.iter().enumerate() {
            // find receiver state in the network state data structure
            let receiver_state = self.state
                .iter()
                .find(|state_entry| state_entry.id == *receiver_id)
                .unwrap();

            let rekey_compute_time = std::time::Instant::now();
            let new_bls_secret_key = Self::process_rekey_messages(
                receiver_index as u64,
                &receiver_state.elgamal_secret_key,
                &dkg_messages,
                &next_pks,
                &next_ids,
                &cache
            );
            println!("computation requirement per node: {:?}", rekey_compute_time.elapsed());
            
            //TODO: need to derive this from the commitments in the DKG messages
            let new_bls_public_key = G::generator().mul(new_bls_secret_key).into_affine();

            let new_state = NodeState {
                id: *receiver_id,
                elgamal_secret_key: receiver_state.elgamal_secret_key.clone(),
                bls_secret_key: Some(new_bls_secret_key),
            };

            let new_addr_book_entry = AddrBookEntry {
                id: *receiver_id,
                pk: self.candidate_addr_book.iter().find(|entry| entry.id == *receiver_id).unwrap().pk,
                commitment: Some(new_bls_public_key),
            };

            next_network_state.push(new_state);
            next_addr_book.push(new_addr_book_entry);
        }

        self.state = next_network_state;

        // let's set candidate to be same as active
        self.addr_book = next_addr_book.clone();
        self.candidate_addr_book = next_addr_book.clone();
    }


    fn process_rekey_messages(
        receiver_index: u64,
        elgamal_secret_key: &ElGamalSecretKey<G>,
        dkg_messages: &Vec<DKGMessage<G>>,
        pks: &Vec<ElGamalPublicKey<G>>,
        ids: &Vec<NodeId<G>>,
        cache: &ElGamalCache<G>,
    ) -> BlsSecretKey<G> {

        //let's verify the messages first
        for message in dkg_messages.iter() {
            let combined_ctxt = ElGamal::<G>::combine_chunked_ciphertext(&message.ctxt);
            let statement: nizk::Statement<G> = nizk::Statement {
                ids: ids.clone(),
                public_keys: pks.clone(),
                polynomial_commitment: message.commitment.clone(),
                ciphertext_values: combined_ctxt.c2,
                ciphertext_rand: combined_ctxt.c1,
            };

            // for genesis, let's expect all parties to behave correctly
            // that said, this can be modified to just include the correct parties
            assert!(verify(&statement, &message.proof));
        }

        let mut incoming_shares: Vec<(NodeId<G>, ElGamalSecretKey<G>)> = Vec::new();

        // let's simulate the work of a receiver, which has to decrypt each dealer's message
        for dkg_message in dkg_messages.iter() {
            let share_y = ElGamal::<G>::chunked_decrypt_multi_receiver(
                receiver_index,
                elgamal_secret_key,
                &dkg_message.ctxt,
                cache
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

        let shares: Vec<(NodeId<G>, BlsSecretKey<G>)> = network_state
            .iter()
            .filter(|state| state.bls_secret_key.is_some())
            .map(|node_state| { (node_state.id.clone(), node_state.bls_secret_key.unwrap())})
            .collect();

        sss::recover::<BlsSecretKey<G>>(&shares)
    }

    #[test]
    fn test_dkg_large() {
        let rng = &mut test_rng();
        let network_size = 32;

        let mut network = GrothDKG::<G>::init();

        // let's add network_size number of nodes
        for _i in 0..network_size {
            let sk = ElGamalSecretKey::<G>::rand(rng);
            network.add_node(&sk);
        }

        // run the genesis protocol
        network.setup(rng);

        // ledger id is the BLS public key // TODO: add the method for getting the public key
        let ledger_id_secret = simulate_bls_secret_recovery(&network.state);

        // let's do a rekey with the same set of nodes
        network.rekey(rng);

        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));
    }

    #[test]
    fn test_dkg_remove() {
        let rng = &mut test_rng();
        let initial_network_size = 5;

        let mut network = GrothDKG::<G>::init();

        for _i in 0..initial_network_size {
            network.add_node(&ElGamalSecretKey::<G>::rand(rng));
        }

        network.setup(rng);
        let ledger_id_secret = simulate_bls_secret_recovery(&network.state);

        // let's first do a rekey with the same set of nodes...because why not!
        network.rekey(rng);
        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));

        // let's remove a node (say node 0) and rekey
        let id_to_be_removed = network.addr_book[0].id;
        network.remove_node(&id_to_be_removed);

        network.rekey(rng);
        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));

        // let's add two nodes and rekey
        network.add_node(&ElGamalSecretKey::<G>::rand(rng));
        network.add_node(&ElGamalSecretKey::<G>::rand(rng));

        network.rekey(rng);
        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));

    }

    #[test]
    fn test_dkg_add() {

        let rng = &mut test_rng();
        let initial_network_size = 5;

        let mut network = GrothDKG::<G>::init();

        for _i in 0..initial_network_size {
            network.add_node(&ElGamalSecretKey::<G>::rand(rng));
        }

        network.setup(rng);
        let ledger_id_secret = simulate_bls_secret_recovery(&network.state);


        // let's add two nodes and rekey
        for _i in 0..2 {
            network.add_node(&ElGamalSecretKey::<G>::rand(rng));
        }
        network.rekey(rng);
        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));

        // let's add three nodes and rekey
        for _i in 0..3 {
            network.add_node(&ElGamalSecretKey::<G>::rand(rng));
        }
        network.rekey(rng);
        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));
    }
}