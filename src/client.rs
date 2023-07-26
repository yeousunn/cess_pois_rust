pub mod acc;
pub mod expanders;
pub mod pois;
pub mod tree;
pub mod util;

use crate::util::parse_key;
use crate::{
    acc::RsaKey,
    pois::{
        prove::{AccProof, Commit, CommitProof},
        verify::Verifier,
    },
};
use acc::multi_level_acc::WitnessNode;
use anyhow::Result;
use bridge::bridge_client::BridgeClient;
use bridge::{Challenge, EmptyRequest, Int64Slice};
use pois::prove::{DeletionProof, MhtProof, SpaceProof};

pub mod bridge {
    tonic::include_proto!("bridge");
}

#[tokio::main]
async fn main() -> Result<()> {
    let mut client = BridgeClient::connect("http://[::1]:50051").await?;

    let (mut verifier, key, id) = init_fields();

    let request = tonic::Request::new(EmptyRequest {});
    let response = client.call_get_commits(request).await?;
    let commit_group = response.into_inner();
    let mut commits = convert_to_commit(commit_group.commit);
    let acc_bytes = commit_group.prover_acc.unwrap().acc;

    verifier.register_prover_node(id, key.clone(), &acc_bytes, 0, 0);

    if !verifier.receive_commits(id, &mut commits) {
        assert!(false);
    }

    let result = verifier.commit_challenges(id, 0, 4);

    if let Ok(chals) = result {
        let challenge = convert_to_challenge(chals.clone());

        let request = tonic::Request::new(challenge);
        let response = client.call_prove_commit_and_acc(request).await?;

        let commit_and_acc_proof = response.into_inner();
        let commit_proof_group_inner = commit_and_acc_proof
            .commit_proof_group
            .unwrap()
            .commit_proof_group_inner;
        let mut commit_proofs = Vec::new();

        for inner in commit_proof_group_inner {
            let mut commit_proof_row = Vec::new();
            for commit_proof in inner.commit_proof {
                commit_proof_row.push(convert_to_commit_proof(&commit_proof));
            }
            commit_proofs.push(commit_proof_row);
        }

        if let Err(err) = verifier.verify_commit_proofs(id, chals.clone(), commit_proofs.clone()) {
            println!("RESPONSE= {:?}", err);
        }

        let pb_acc_proof = commit_and_acc_proof.acc_proof.unwrap();
        let acc_proof = convert_to_acc_proof(&pb_acc_proof);
        if let Err(err) = verifier.verify_acc(id, chals, acc_proof) {
            println!("RESPONSE= {:?}", err);
        }
    }

    let space_chals = verifier.space_challenges(22);
    if let Ok(space_chals) = space_chals {
        let mut int64_slice = Int64Slice::default();
        int64_slice.values = space_chals.clone();
        let request = tonic::Request::new(int64_slice);
        let response = client.call_prove_space(request).await?;
        let bridge_space_proof = response.into_inner();

        let mut space_proof = convert_to_space_proof(&bridge_space_proof);

        if let Ok(p_node) = verifier.get_node(id) {
            if let Err(err) = verifier.verify_space(p_node, space_chals, &mut space_proof) {
                println!("A RESPONSE= {:?}", err);
            }
        }
    }

    let request = tonic::Request::new(EmptyRequest {});
    let response = client.call_prove_deletion(request).await;
    match response {
        Ok(response) => {
            let bridge_del_proof = response.into_inner();
            let mut del_proof = convert_to_deletion_proof(&bridge_del_proof);
            if let Err(err) = verifier.verify_deletion(id, &mut del_proof) {
                println!("RESPONSE= {:?}", err);
            }
        }
        Err(e) => {
            println!("RESPONSE= {:?}", e);
        }
    }
    Ok(())
}

pub fn convert_to_deletion_proof(pb_proof: &bridge::DeletionProof) -> DeletionProof {
    let mut roots: Vec<Vec<u8>> = Vec::new();
    for root in &pb_proof.roots {
        roots.push(root.to_vec());
    }

    let wit_chain = convert_to_witness_node(&pb_proof.wit_chain.as_ref().unwrap());

    let mut acc_path: Vec<Vec<u8>> = Vec::new();
    for path in &pb_proof.acc_path {
        acc_path.push(path.to_vec());
    }

    DeletionProof {
        roots,
        wit_chain,
        acc_path,
    }
}

pub fn convert_to_space_proof(message: &bridge::SpaceProof) -> SpaceProof {
    let mut proofs = Vec::new();
    for proof_group in &message.proofs {
        let mut mht_proof_group = Vec::new();
        for proof in &proof_group.proofs {
            let mht_proof = MhtProof {
                index: proof.index,
                label: proof.label.clone(),
                paths: proof.paths.clone(),
                locs: proof.locs.clone(),
            };
            mht_proof_group.push(mht_proof);
        }
        proofs.push(mht_proof_group);
    }

    let roots = message.roots.clone();

    let mut wit_chains = Vec::new();
    for wit_chain in &message.wit_chains {
        let witness_node = convert_to_witness_node(wit_chain);
        wit_chains.push(witness_node);
    }

    SpaceProof {
        left: message.left,
        right: message.right,
        proofs,
        roots,
        wit_chains,
    }
}

fn convert_to_acc_proof(pb_acc_proof: &bridge::AccProof) -> AccProof {
    let indexs = pb_acc_proof.indexs.to_vec();
    let labels = pb_acc_proof.labels.to_vec();
    let wit_chains = if let Some(pb_wit_chains) = &pb_acc_proof.wit_chains {
        Some(Box::new(convert_to_witness_node(pb_wit_chains)))
    } else {
        None
    };
    let acc_path = pb_acc_proof.acc_path.to_vec();

    AccProof {
        indexs,
        labels,
        wit_chains,
        acc_path,
    }
}

fn convert_to_witness_node(pb_witness_node: &bridge::AccWitnessNode) -> WitnessNode {
    let elem = pb_witness_node.elem.to_vec();
    let wit = pb_witness_node.wit.to_vec();
    let acc = if let Some(pb_acc) = &pb_witness_node.acc {
        Some(Box::new(convert_to_witness_node(pb_acc)))
    } else {
        None
    };

    WitnessNode { elem, wit, acc }
}

fn convert_to_mht_proof(pb_proof: &bridge::MhtProof) -> MhtProof {
    MhtProof {
        index: pb_proof.index,
        label: pb_proof.label.clone(),
        paths: pb_proof.paths.iter().cloned().collect(),
        locs: pb_proof.locs.clone(),
    }
}

fn convert_to_commit_proof(pb_commit_proof: &bridge::CommitProof) -> CommitProof {
    CommitProof {
        node: convert_to_mht_proof(&pb_commit_proof.node.as_ref().unwrap()),
        parents: pb_commit_proof
            .parents
            .iter()
            .map(|pb_parent| convert_to_mht_proof(pb_parent))
            .collect(),
    }
}

fn convert_to_commit(commits: Vec<bridge::Commit>) -> Vec<Commit> {
    let mut converted_commits = Vec::new();

    for commit in commits {
        let converted_commit = Commit {
            file_index: commit.file_index,
            roots: commit.roots,
        };

        converted_commits.push(converted_commit);
    }

    converted_commits
}

fn convert_to_challenge(chals: Vec<Vec<i64>>) -> Challenge {
    let mut challenge = Challenge::default();
    for row in chals {
        let mut int64_slice = Int64Slice::default();
        int64_slice.values = row;
        challenge.rows.push(int64_slice);
    }

    challenge
}

fn init_fields() -> (Verifier, RsaKey, &'static [u8]) {
    let verifier = Verifier::new(1, 512, 32);
    // let key = acc::rsa_keygen(2048);
    let key = parse_key("./key").unwrap();
    let id = b"test miner id";

    (verifier, key, id)
}
