use rand::Rng;

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
    pub dealer_id: ShareId<G>,
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
    pub share_id: ShareId<G>, // unique id for the node
    pub elgamal_public_key: ElGamalPublicKey<G>, // ElGamal public key
    pub bls_public_key: Option<BlsPublicKey<G>>, // commitment to the BLS key share
}

pub type AddrBook<G> = Vec<AddrBookEntry<G>>;

#[derive(Clone)]
pub struct ShareState<G: CurveGroup> {
    pub id: ShareId<G>,
    pub elgamal_secret_key: ElGamalSecretKey<G>,
    pub bls_secret_key: Option<BlsSecretKey<G>>,
}

// only used for simulation purposes, real protocol does not have this!
pub type NetworkState<G> = Vec<ShareState<G>>;

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
        let ids = self.candidate_addr_book.iter().map(|entry| entry.share_id).collect::<Vec<ShareId<G>>>();
        // all public keys, arranged by the above ids
        let pks = self.candidate_addr_book.iter().map(|entry| entry.elgamal_public_key).collect::<Vec<ElGamalPublicKey<G>>>();

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
                    dealer_id: dealer_entry.share_id.clone(),
                    proof: prove(&witness, &statement, rng),
                    commitment: poly_commitment.clone(),
                }
            );
        }

        // let's compute the next address book and network state
        let mut genesis_network_state = NetworkState::<G>::new();
        let mut genesis_addr_book = AddrBook::<G>::new();
        let cache = ElGamal::<G>::generate_cache();

        let valid_dkg_messages: Vec<&DKGMessage<G>> = dkg_messages
            .iter()
            .filter(|msg| Self::verify_dkg_message(
                msg,
                &pks,
                &ids,
                &self.candidate_addr_book.iter().find(|entry| entry.share_id == msg.dealer_id).unwrap().bls_public_key)
            )
            .collect();

        println!("[setup] valid dkg messages: {:?}", valid_dkg_messages.len());

        for (receiver_index, receiver_id) in ids.iter().enumerate() {
            // find receiver state in the network state data structure
            let receiver_state = self.state
                .iter()
                .find(|state_entry| state_entry.id == *receiver_id)
                .unwrap();

            let new_bls_secret_key = Self::process_setup_messages(
                receiver_index as u64,
                &receiver_state.elgamal_secret_key,
                &valid_dkg_messages,
                &cache
            );
            
            let new_bls_public_key = Self::compute_share_public_key_setup(&valid_dkg_messages, receiver_id);
            assert!(new_bls_public_key == G::generator().mul(&new_bls_secret_key).into_affine());

            let new_state = ShareState {
                id: *receiver_id,
                elgamal_secret_key: receiver_state.elgamal_secret_key.clone(),
                bls_secret_key: Some(new_bls_secret_key),
            };

            let new_addr_book_entry = AddrBookEntry {
                share_id: *receiver_id,
                elgamal_public_key: self.candidate_addr_book.iter().find(|entry| entry.share_id == *receiver_id).unwrap().elgamal_public_key,
                bls_public_key: Some(new_bls_public_key),
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
    pub fn add_node(&mut self, elgamal_secret_key: &ElGamalSecretKey<G>) {
        let elgamal_public_key = G::generator().mul(elgamal_secret_key).into_affine();

        // let's give this node a brand new id, which is 1 more than the maximum id in the address book
        let max_existing_id = self.candidate_addr_book
            .iter()
            .map(|entry| entry.share_id)
            .max()
            .unwrap_or(ShareId::<G>::zero());

        let node_id = max_existing_id + ShareId::<G>::one();

        // we only touch the candidate addr_book
        self.candidate_addr_book.push(AddrBookEntry {
            share_id: node_id.clone(),
            elgamal_public_key: elgamal_public_key,
            bls_public_key: None,
        });
        
        self.state.push(ShareState {
            id: node_id.clone(),
            elgamal_secret_key: elgamal_secret_key.clone(),
            bls_secret_key: None,
        });
    }

    pub fn remove_node(&mut self, node_id: &ShareId<G>) {
        // collect all entries that are not the node_id to be removed
        let all_but_nodeid_addr_book = self.candidate_addr_book
            .iter()
            .filter(|entry| entry.share_id != *node_id)
            .cloned()
            .collect::<AddrBook<G>>();

        // we only touch the candidate addr_book
        self.candidate_addr_book = all_but_nodeid_addr_book;
    }

    pub fn rekey<R: Rng>(&mut self, rng: &mut R) {

        let next_n = self.candidate_addr_book.len();
        let next_t = next_n / 2 + 1;
        
        // all node ids as field elements
        let next_ids = self.candidate_addr_book.iter().map(|entry| entry.share_id).collect::<Vec<ShareId<G>>>();
        // all public keys, arranged by the above ids
        let next_pks = self.candidate_addr_book.iter().map(|entry| entry.elgamal_public_key).collect::<Vec<ElGamalPublicKey<G>>>();

        let mut dkg_messages = Vec::new();

        // let's simulate the work of all dealers
        for dealer_entry in self.addr_book.iter() {

            // each dealer will secret-share its bls secret key
            let bls_secret = self.state
                .iter()
                .find(|state| state.id == dealer_entry.share_id)
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
                    dealer_id: dealer_entry.share_id.clone(),
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
        println!("dkg messages: {:?}", dkg_messages.len());

        // let's compute the output address book and network state
        let mut next_network_state = NetworkState::<G>::new();
        let mut next_addr_book = AddrBook::<G>::new();

        let cache = ElGamal::<G>::generate_cache();

        let valid_dkg_messages: Vec<&DKGMessage<G>> = dkg_messages
            .iter()
            .filter(|msg| Self::verify_dkg_message(
                msg,
                &next_pks,
                &next_ids,
                &self.addr_book.iter().find(|entry| entry.share_id == msg.dealer_id).unwrap().bls_public_key)
            )
            .collect();
        println!("valid dkg messages: {:?}", valid_dkg_messages.len());

        for (receiver_index, receiver_id) in next_ids.iter().enumerate() {
            // find receiver state in the network state data structure
            let receiver_state = self.state
                .iter()
                .find(|state_entry| state_entry.id == *receiver_id)
                .unwrap();

            let rekey_compute_time = std::time::Instant::now();
            let new_bls_secret_key = Self::compute_share_secret_key(
                receiver_index as u64,
                &receiver_state.elgamal_secret_key,
                &valid_dkg_messages,
                &cache
            );
            
            let new_bls_public_key = Self::compute_share_public_key_rekey(&valid_dkg_messages, receiver_id);
            assert!(new_bls_public_key == G::generator().mul(&new_bls_secret_key).into_affine());

            println!("computation requirement per node: {:?}", rekey_compute_time.elapsed());

            let new_state = ShareState {
                id: *receiver_id,
                elgamal_secret_key: receiver_state.elgamal_secret_key.clone(),
                bls_secret_key: Some(new_bls_secret_key),
            };

            let new_addr_book_entry = AddrBookEntry {
                share_id: *receiver_id,
                elgamal_public_key: self.candidate_addr_book.iter().find(|entry| entry.share_id == *receiver_id).unwrap().elgamal_public_key,
                bls_public_key: Some(new_bls_public_key),
            };

            next_network_state.push(new_state);
            next_addr_book.push(new_addr_book_entry);
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

            incoming_shares.push((dkg_message.dealer_id.clone(), share_y));
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
            dealer_ids.push(msg.dealer_id);
        }

        let λs: Vec<ShareId<G>> = (0..dealer_ids.len()).map(|i| { lagrange_coefficient(&dealer_ids, i, ShareId::<G>::zero()) }).collect();

        let public_key = λs.iter().zip(dealt_share_pubkeys.iter())
            .fold(G::zero(), |acc, (&λ_i, &y_i)| { acc + y_i.mul(λ_i) });

        return public_key.into_affine();
    }

    pub fn compute_ledger_id(&self) -> BlsPublicKey<G> {
        // all node ids as field elements
        let ids = self.addr_book.iter().map(|entry| entry.share_id).collect::<Vec<ShareId<G>>>();
        // all public keys, arranged by the above ids
        let pks = self.addr_book.iter().map(|entry| entry.bls_public_key.unwrap()).collect::<Vec<BlsPublicKey<G>>>();

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

        let shares: Vec<(ShareId<G>, BlsSecretKey<G>)> = network_state
            .iter()
            .filter(|state| state.bls_secret_key.is_some())
            .map(|node_state| { (node_state.id.clone(), node_state.bls_secret_key.unwrap())})
            .collect();

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
            network.add_node(&sk);
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
            network.add_node(&ElGamalSecretKey::<G>::rand(rng));
        }

        network.setup(rng);
        let ledger_id = network.compute_ledger_id();
        let ledger_id_secret = simulate_bls_secret_recovery(&network.state);

        // let's first do a rekey with the same set of nodes...because why not!
        network.rekey(rng);
        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));
        assert_eq!(ledger_id, network.compute_ledger_id());

        // let's remove a node (say node 0) and rekey
        let id_to_be_removed = network.addr_book[0].share_id;
        network.remove_node(&id_to_be_removed);

        network.rekey(rng);
        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));
        assert_eq!(ledger_id, network.compute_ledger_id());

        // let's add two nodes and rekey
        network.add_node(&ElGamalSecretKey::<G>::rand(rng));
        network.add_node(&ElGamalSecretKey::<G>::rand(rng));

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
            network.add_node(&ElGamalSecretKey::<G>::rand(rng));
        }

        network.setup(rng);
        let ledger_id = network.compute_ledger_id();
        let ledger_id_secret = simulate_bls_secret_recovery(&network.state);

        // let's add two nodes and rekey
        for _i in 0..2 {
            network.add_node(&ElGamalSecretKey::<G>::rand(rng));
        }
        network.rekey(rng);
        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));
        assert_eq!(ledger_id, network.compute_ledger_id());

        // let's add three nodes and rekey
        for _i in 0..3 {
            network.add_node(&ElGamalSecretKey::<G>::rand(rng));
        }
        network.rekey(rng);
        assert_eq!(ledger_id_secret, simulate_bls_secret_recovery(&network.state));
        assert_eq!(ledger_id, network.compute_ledger_id());
    }
}