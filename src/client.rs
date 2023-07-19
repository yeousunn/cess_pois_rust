pub mod acc;
pub mod expanders;
pub mod pois;
pub mod tree;
pub mod util;

use anyhow::Result;
use acc::multi_level_acc::WitnessNode;
use bridge::bridge_client::BridgeClient;
use bridge::{Challenge, Int64Slice, EmptyRequest};
use pois::prove::{MhtProof, SpaceProof, DeletionProof};
use crate::util::parse_key;
use crate::{
    acc::RsaKey,
    pois::{
        prove::{AccProof, Commit, CommitProof},
        verify::Verifier,
    },
};

pub mod bridge {
    tonic::include_proto!("bridge");
}

#[tokio::main]
async fn main() -> Result<()> {
    let mut client = BridgeClient::connect("http://[::1]:50051").await?;

    let (mut verifier, key, id) = init_fields();

    let request = tonic::Request::new(EmptyRequest {  });
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
        let commit_proof_group_inner = commit_and_acc_proof.commit_proof_group.unwrap().commit_proof_group_inner;
        let mut commit_proofs = Vec::new();

        for inner in commit_proof_group_inner {
            let mut commit_proof_row = Vec::new();
            for commit_proof in inner.commit_proof {
                commit_proof_row.push(convert_to_commit_proof(&commit_proof));
            }
            commit_proofs.push(commit_proof_row);
        }

        if let Err(err) = verifier.verify_commit_proofs(id, chals.clone(), commit_proofs.clone()){
            println!("RESPONSE= {:?}", err);
        }
        
        let pb_acc_proof = commit_and_acc_proof.acc_proof.unwrap();
        let acc_proof = convert_to_acc_proof(&pb_acc_proof);
        if let Err(err) = verifier.verify_acc(id, chals, acc_proof){
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

    let request = tonic::Request::new(EmptyRequest {  });
    let response = client.call_prove_deletion(request).await?;
    let bridge_del_proof = response.into_inner();
    let mut del_proof = convert_to_deletion_proof(&bridge_del_proof);
    println!("del_proof: {:?}", del_proof);
    if let Err(err) = verifier.verify_deletion(id, &mut del_proof) {
        println!("RESPONSE= {:?}", err);
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
        parents: pb_commit_proof.parents.iter().map(|pb_parent| convert_to_mht_proof(pb_parent)).collect(),
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

// fn init_commit() -> Vec<Commit> {
//     vec![
//         Commit {
//             file_index: 1,
//             roots: vec![
//                 vec![
//                     129, 208, 232, 95, 249, 86, 213, 83, 196, 183, 29, 167, 7, 68, 69, 253,
//                     202, 194, 114, 209, 12, 234, 236, 200, 234, 136, 131, 42, 252, 192, 106,
//                     183, 1, 225, 160, 241, 63, 63, 237, 90, 209, 169, 157, 51, 1, 30, 97, 215,
//                     220, 120, 179, 37, 221, 146, 223, 90, 158, 226, 11, 98, 180, 95, 74, 118,
//                 ],
//                 vec![
//                     157, 6, 210, 195, 248, 145, 203, 9, 148, 45, 218, 23, 43, 170, 214, 42, 81,
//                     70, 47, 161, 197, 124, 111, 169, 120, 23, 193, 16, 2, 154, 214, 95, 166,
//                     211, 80, 83, 60, 195, 205, 1, 158, 126, 11, 165, 80, 126, 25, 172, 216,
//                     124, 227, 27, 52, 161, 100, 57, 200, 5, 187, 206, 58, 233, 122, 153,
//                 ],
//                 vec![
//                     207, 152, 225, 28, 141, 61, 43, 90, 16, 214, 39, 205, 43, 214, 206, 87,
//                     192, 92, 210, 120, 43, 239, 115, 26, 123, 205, 180, 12, 43, 80, 236, 183,
//                     6, 173, 120, 87, 249, 28, 125, 180, 5, 116, 132, 126, 231, 205, 181, 220,
//                     98, 108, 173, 3, 25, 163, 102, 39, 221, 78, 121, 19, 4, 145, 229, 202,
//                 ],
//             ],
//         },
//         Commit {
//             file_index: 2,
//             roots: vec![
//                 vec![
//                     105, 194, 234, 123, 181, 216, 213, 65, 169, 242, 197, 188, 176, 54, 62,
//                     155, 117, 249, 61, 34, 137, 31, 10, 141, 232, 236, 188, 127, 133, 106, 50,
//                     136, 127, 143, 186, 246, 209, 76, 103, 92, 42, 40, 115, 166, 227, 161, 33,
//                     233, 175, 25, 72, 25, 232, 1, 219, 82, 21, 117, 143, 208, 252, 196, 225,
//                     238,
//                 ],
//                 vec![
//                     136, 182, 14, 188, 56, 232, 174, 221, 83, 60, 134, 111, 147, 35, 128, 172,
//                     2, 51, 156, 120, 132, 152, 46, 69, 235, 112, 133, 122, 200, 46, 239, 173,
//                     53, 188, 148, 9, 45, 128, 1, 133, 160, 175, 105, 29, 4, 34, 75, 59, 81, 41,
//                     100, 90, 69, 241, 31, 174, 96, 103, 138, 41, 120, 222, 227, 242,
//                 ],
//                 vec![
//                     204, 129, 223, 155, 138, 218, 139, 118, 30, 100, 113, 96, 75, 161, 67, 233,
//                     223, 30, 205, 155, 171, 164, 32, 161, 16, 22, 148, 215, 184, 252, 228, 5,
//                     86, 11, 113, 179, 106, 240, 183, 89, 125, 217, 10, 185, 33, 211, 230, 177,
//                     159, 69, 69, 156, 48, 53, 112, 190, 133, 38, 227, 98, 237, 90, 209, 185,
//                 ],
//             ],
//         },
//         Commit {
//             file_index: 3,
//             roots: vec![
//                 vec![
//                     251, 152, 192, 124, 183, 126, 22, 198, 131, 59, 208, 40, 164, 228, 231, 99,
//                     112, 26, 234, 125, 203, 172, 190, 150, 185, 202, 217, 198, 186, 153, 72,
//                     25, 59, 101, 254, 180, 180, 232, 105, 217, 144, 187, 236, 248, 211, 175,
//                     180, 246, 130, 160, 168, 116, 105, 44, 115, 118, 93, 254, 193, 146, 165,
//                     75, 56, 123,
//                 ],
//                 vec![
//                     62, 35, 50, 182, 151, 147, 96, 102, 173, 210, 115, 32, 65, 69, 212, 130,
//                     140, 77, 172, 92, 243, 89, 169, 101, 68, 16, 247, 69, 92, 202, 121, 139,
//                     197, 53, 76, 106, 152, 48, 99, 122, 189, 146, 157, 14, 128, 4, 146, 7, 97,
//                     55, 157, 57, 177, 5, 77, 213, 38, 122, 174, 166, 124, 63, 104, 1,
//                 ],
//                 vec![
//                     107, 227, 158, 56, 129, 159, 81, 61, 181, 91, 239, 161, 166, 155, 110, 33,
//                     4, 32, 24, 253, 168, 157, 164, 153, 57, 203, 136, 197, 239, 72, 247, 47,
//                     141, 7, 161, 181, 37, 62, 3, 248, 187, 143, 7, 77, 237, 225, 49, 7, 146,
//                     80, 237, 188, 152, 177, 161, 6, 116, 111, 120, 171, 221, 171, 63, 42,
//                 ],
//             ],
//         },
//         Commit {
//             file_index: 4,
//             roots: vec![
//                 vec![
//                     231, 160, 10, 151, 1, 121, 163, 135, 116, 207, 59, 124, 55, 31, 112, 54,
//                     136, 114, 51, 75, 86, 103, 132, 173, 38, 11, 207, 98, 176, 63, 108, 251,
//                     130, 246, 221, 74, 118, 119, 65, 123, 110, 175, 223, 44, 24, 24, 155, 255,
//                     241, 210, 144, 225, 94, 124, 22, 8, 224, 13, 113, 31, 191, 44, 31, 254,
//                 ],
//                 vec![
//                     36, 214, 131, 14, 174, 60, 168, 239, 13, 45, 194, 136, 212, 28, 119, 44,
//                     105, 171, 83, 140, 116, 121, 125, 44, 99, 118, 124, 65, 179, 139, 212, 25,
//                     86, 155, 41, 92, 39, 240, 75, 221, 118, 26, 216, 82, 83, 231, 86, 25, 181,
//                     239, 80, 129, 167, 30, 51, 75, 58, 23, 155, 237, 116, 43, 138, 214,
//                 ],
//                 vec![
//                     52, 149, 50, 251, 125, 102, 147, 71, 37, 245, 21, 80, 173, 30, 2, 101, 18,
//                     106, 139, 106, 251, 27, 250, 121, 187, 135, 22, 131, 114, 213, 12, 206,
//                     228, 232, 79, 246, 222, 74, 119, 49, 125, 21, 9, 95, 143, 189, 239, 80,
//                     193, 157, 218, 93, 233, 230, 227, 236, 2, 114, 84, 200, 99, 92, 167, 177,
//                 ],
//             ],
//         },
//     ]
// }