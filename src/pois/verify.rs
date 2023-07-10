use anyhow::{anyhow, bail, Context, Ok, Result};
use core::panic;
use merkle_light::hash;
use rand::Rng;
use sha2::{Digest, Sha512};
use std::collections::HashMap;
use std::mem;

use super::prove::{AccProof, Commit, CommitProof, DeletionProof, SpaceProof};
use crate::acc::multi_level_acc::{verify_delete_update, verify_mutilevel_acc, verify_insert_update};
use crate::acc::RsaKey;
// use crate::acc::multi_level_acc::verify_insert_update;
use crate::expanders::generate_idle_file::{get_hash, HASH_SIZE};
use crate::expanders::{
    generate_expanders::calc_parents as generate_expanders_calc_parents,
    generate_idle_file::{new_hash, Hasher as ExpanderHasher},
    Expanders,
};
use crate::expanders::{get_bytes, NodeType};
use crate::tree::{check_index_path, verify_path_proof, PathProof};
use crate::util::copy_data;
use crate::{acc, expanders};

pub const MAX_BUF_SIZE: i32 = 1 * 16;
pub static mut SPACE_CHALS: i64 = 22;
pub const PICK: i32 = 1;

#[derive(Clone, Debug)]
pub struct Record {
    pub key: acc::RsaKey,
    pub acc: Vec<u8>,
    pub front: i64,
    pub rear: i64,
    pub record: i64,
}
#[derive(Clone, Debug)]
pub struct ProverNode {
    pub id: Vec<u8>,
    pub commit_buf: Vec<Commit>,
    pub buf_size: i32,
    pub record: Option<Record>,
}

#[derive(Clone, Debug)]
pub struct Verifier {
    pub expanders: Expanders,
    pub nodes: HashMap<String, ProverNode>,
}

impl Verifier {
    pub fn new(k: i64, n: i64, d: i64) -> Self {
        unsafe {
            SPACE_CHALS = (n as f64).log2().floor() as i64;
        }

        Verifier {
            expanders: Expanders::new(k, n, d),
            nodes: HashMap::new(),
        }
    }

    pub fn register_prover_node(
        &mut self,
        id: &[u8],
        key: RsaKey,
        acc: &[u8],
        front: i64,
        rear: i64,
    ) {
        let node = ProverNode::new(&id, key, acc, front, rear);
        let id = hex::encode(id);
        self.nodes.insert(id, node);
    }

    pub fn get_mode(&self, id: &[u8]) -> Result<&ProverNode> {
        let id = hex::encode(id);
        let node = self
            .nodes
            .get(&id)
            .with_context(|| format!("Node not found."))?;
        Ok(node)
    }

    pub fn is_logout(&self, id: &[u8]) -> bool {
        let id = hex::encode(id);
        !self.nodes.contains_key(&id)
    }

    pub fn logout_prover_node(&self, id: &[u8]) -> Result<(Vec<u8>, i64, i64)> {
        let id = hex::encode(id);
        let node = self
            .nodes
            .get(&id)
            .with_context(|| format!("Node not found."))?;

        let (acc, front, rear) = match &node.record {
            Some(record) => (record.acc.clone(), record.front, record.rear),
            None => panic!("Record not found."),
        };

        Ok((acc, front, rear))
    }

    pub fn receive_commits(&mut self, id: &[u8], commits: &mut [Commit]) -> bool {
        let id = hex::encode(id);

        let p_node = match self.nodes.get(&id) {
            Some(node) => node.clone(),
            None => return false,
        };

        if !p_node.id.eq(&hex::decode(id).unwrap()) {
            return false;
        }

        let mut is_valid_commit = false;
        if commits.len() > (MAX_BUF_SIZE - p_node.buf_size) as usize {
            let commits = &mut commits[..(MAX_BUF_SIZE - p_node.buf_size) as usize];
            is_valid_commit = self.validate_commit(&p_node, commits);
        } else {
            is_valid_commit = self.validate_commit(&p_node, commits);
        }

        is_valid_commit
    }

    fn validate_commit(&mut self, p_node: &ProverNode, commits: &mut [Commit]) -> bool {
        let mut p_node = p_node.clone();
        for i in 0..commits.len() {
            if commits[i].file_index <= p_node.record.as_ref().unwrap().front {
                return false;
            }

            if commits[i].roots.len() != (self.expanders.k + 2) as usize {
                return false;
            }
            // TODO: find a way to reset the hasher instead of creating new object
            let hash = new_hash();
            let result = match hash {
                // TODO: write a generic function for the below task.
                ExpanderHasher::SHA256(hash) => {
                    let mut hash = hash;
                    for j in 0..commits[i].roots.len() - 1 {
                        hash.update(&commits[i].roots[j]);
                    }

                    let result = hash.finalize();
                    result.to_vec()
                }
                ExpanderHasher::SHA512(hash) => {
                    let mut hash = hash;
                    for j in 0..commits[i].roots.len() - 1 {
                        hash.update(&commits[i].roots[j]);
                    }

                    let result = hash.finalize();
                    result.to_vec()
                }
            };

            if commits[i].roots[self.expanders.k as usize + 1] != result[..] {
                return false;
            }

            p_node.commit_buf.push(commits[i].clone());
            p_node.buf_size += 1;
        }
        if let Some(node) = self.nodes.get_mut(&hex::encode(&p_node.id)) {
            *node = p_node;
        }

        true
    }

    pub fn commit_challenges(&mut self, id: &[u8], left: i32, right: i32) -> Result<Vec<Vec<i64>>> {
        let id = hex::encode(id);
        let p_node = self
            .nodes
            .get(&id)
            .with_context(|| format!("Prover node not found"))?;

        if right - left <= 0 || right > p_node.buf_size || left < 0 {
            let err = anyhow!("bad file number");
            bail!("generate commit challenges error: {}", err);
        }
        let mut challenges: Vec<Vec<i64>> = Vec::with_capacity((right - left) as usize);
        let mut rng = rand::thread_rng();
        for i in left..right {
            // let idx = i - left;
            let mut inner_vec = vec![0; self.expanders.k as usize + 2];
            inner_vec[0] = p_node.commit_buf[i as usize].file_index;
            let r = rng.gen_range(0..self.expanders.n);
            inner_vec[1] = r + self.expanders.n * self.expanders.k;

            for j in 2..=(self.expanders.k + 1) as usize {
                let r = rng.gen_range(0..(self.expanders.d + 1));
                inner_vec[j] = r;
            }

            challenges.push(inner_vec);
        }
        Ok(challenges)
    }

    pub fn space_challenges(&self, params: i64) -> Result<Vec<i64>> {
        //let mut inner_vec = vec![0; self.expanders.k as usize + 2];
        let mut challenges: Vec<i64> = vec![0; params as usize];
        let mut mp: HashMap<i64, ()> = HashMap::new();
        let mut rng = rand::thread_rng();
        for i in 0..params {
            loop {
                let mut r = rng.gen_range(0..self.expanders.n);
                if mp.contains_key(&r) {
                    continue;
                }
                mp.insert(r, ());
                r += self.expanders.n * self.expanders.k;
                challenges[i as usize] = r;
                break;
            }
        }

        Ok(challenges)
    }

    pub fn verify_commit_proofs(
        &self,
        id: &[u8],
        chals: Vec<Vec<i64>>,
        proofs: Vec<Vec<CommitProof>>,
    ) -> Result<()> {
        let id_str = hex::encode(id);
        let p_node = self
            .nodes
            .get(&id_str)
            .with_context(|| format!("Prover node not found"))?;

        if chals.len() != proofs.len() || chals.len() > p_node.buf_size as usize {
            let err = anyhow!("bad proof data");
            bail!("verify commit proofs error: {}", err);
        }

        if let Err(err) = self.verify_node_dependencies(id, chals.clone(), proofs.clone(), PICK) {
            bail!("verify commit proofs error {}", err);
        }

        let mut index = 0;
        for i in 0..p_node.buf_size {
            if chals[0][0] == p_node.commit_buf[i as usize].file_index {
                index = i;
                break;
            }
        }
        let front_side = (mem::size_of::<NodeType>() + id.len() + 8) as i32;
        let hash_size = HASH_SIZE;
        let mut label =
            vec![0; front_side as usize + (self.expanders.d + 1) as usize * hash_size as usize];
        for i in 0..proofs.len() {
            if chals[i][1] != proofs[i][0].node.index as i64 {
                let err = anyhow!("bad expanders node index");
                bail!("verify commit proofs error {}", err);
            }

            let mut idx: NodeType;
            for j in 1..chals[i].len() {
                if j == 1 {
                    idx = chals[i][1] as NodeType;
                } else {
                    idx = proofs[i][j - 2].parents[chals[i][j] as usize].index as NodeType;
                }

                let layer = idx as i64 / self.expanders.n;
                let mut root = &p_node.commit_buf[index as usize + i].roots[layer as usize];
                let path_proof = PathProof {
                    locs: proofs[i][j - 1].node.locs.clone(),
                    path: proofs[i][j - 1].node.paths.clone(),
                };

                if verify_path_proof(root, &proofs[i][j - 1].node.label, path_proof) {
                    let err = anyhow!("verify path proof error");
                    bail!("verify commit proofs error {}", err);
                }

                if proofs[i][j - 1].parents.len() <= 0 {
                    continue;
                }

                copy_data(&mut label, &[id, &get_bytes(chals[i][0]), &get_bytes(idx)]);

                let mut size = front_side;

                for p in &proofs[i][j - 1].parents {
                    if p.index as i64 >= layer * self.expanders.n {
                        root = &p_node.commit_buf[index as usize + i as usize].roots[layer as usize]
                    } else {
                        root = &p_node.commit_buf[index as usize + i as usize].roots
                            [layer as usize - 1]
                    }
                    let path_proof = PathProof {
                        locs: p.locs.clone(),
                        path: p.paths.clone(),
                    };
                    if verify_path_proof(root, &p.label, path_proof) {
                        let err = anyhow!("verify parent path proof error");
                        bail!("verify commit proofs error: {}", err);
                    }
                    label[(size as usize)..(size + HASH_SIZE) as usize].copy_from_slice(&p.label);
                    size += HASH_SIZE
                }
                if !get_hash(&label).eq(&proofs[i][j - 1].node.label) {
                    let err = anyhow!("verify label error");
                    bail!("verify commit proofs error: {}", err);
                }
            }
        }
        Ok(())
    }

    pub fn verify_node_dependencies(
        &self,
        id: &[u8],
        chals: Vec<Vec<i64>>,
        proofs: Vec<Vec<CommitProof>>,
        pick: i32,
    ) -> Result<()> {
        let mut pick = pick;
        if pick as usize > proofs.len() {
            pick = proofs.len() as i32;
        }
        let mut rng = rand::thread_rng();
        for _ in 0..pick {
            let r1 = rng.gen_range(0..proofs.len());
            let r2 = rng.gen_range(0..proofs[r1].len());
            let proof = &proofs[r1][r2];
            let mut node = expanders::Node::new(proof.node.index);
            generate_expanders_calc_parents(&self.expanders, &mut node, id, chals[r1][0]);
            for j in 0..node.parents.len() {
                if node.parents[j] != proof.parents[j].index {
                    let err = anyhow!("node relationship mismatch");
                    bail!("verify node dependencies error: {}", err);
                }
            }
        }
        Ok(())
    }

    pub fn verify_acc(
        &mut self,
        id: &[u8],
        chals: Vec<Vec<i64>>,
        proof: AccProof,
    ) -> Result<()> {
        let id_str = hex::encode(id);

        if let Some(p_node) = self.nodes.get_mut(&id_str) {
            if chals.len() != proof.indexs.len() || chals.len() > p_node.buf_size as usize {
                let err = anyhow!("bad proof data");
                bail!("verify acc proofs error: {}", err);
            }

            let mut index = 0;
            for i in 0..p_node.buf_size {
                if chals[0][0] == p_node.commit_buf[i as usize].file_index {
                    index = i;
                    break;
                }
            }

            let mut label = vec![0u8; id.len() + 8 + HASH_SIZE as usize];

            for i in 0..chals.len() {
                if chals[i][0] != proof.indexs[i] || chals[i][0] != p_node.record.as_ref().unwrap().rear + i as i64 + 1 {
                    let err = anyhow!("bad file index");
                    bail!("verify acc proofs error: {}", err);
                }

                copy_data(
                    &mut label,
                    &[id, &get_bytes(chals[i][0]), &p_node.commit_buf[i + index as usize].roots[self.expanders.k as usize]],
                );

                if !get_hash(&label).eq(&proof.labels[i]) {
                    let err = anyhow!("verify file label error");
                    bail!("verify acc proofs error: {}", err);
                }
            }

            if !verify_insert_update(
                p_node.record.clone().unwrap().key,
                &mut proof.wit_chains.unwrap(),
                proof.labels,
                proof.acc_path.clone(),
                p_node.record.clone().unwrap().acc,
            ) {
                let err = anyhow!("verify muti-level acc error");
                bail!("verify acc proofs error: {}", err);
            }

            p_node.record.as_mut().unwrap().acc = proof.acc_path.last().cloned().unwrap();
            p_node.commit_buf.splice(index as usize..(index as usize + chals.len()) as usize, std::iter::empty());
            p_node.buf_size -= chals.len() as i32;
            p_node.record.as_mut().unwrap().rear += chals.len() as i64;
        } else {
            let err = anyhow!("Prover node not found");
            bail!("verify acc proofs error: {}", err);
        }

        Ok(())
    }

    pub fn verify_space(
        &self,
        p_node: &ProverNode,
        chals: Vec<i64>,
        proof: &SpaceProof,
    ) -> Result<()> {
        if chals.len() <= 0
            || p_node.record.as_ref().unwrap().record + 1 != proof.left
            || p_node.record.as_ref().unwrap().rear + 1 < proof.right
        {
            let err = anyhow!("bad proof data");
            bail!("verify space proofs error: {}", err);
        }
        let mut label: Vec<u8> = Vec::with_capacity(p_node.id.len() + 8 + HASH_SIZE as usize);
        for i in 0..proof.roots.len() {
            for j in 0..chals.len() {
                if chals[j] != proof.proofs[i][j].index as i64 {
                    let err = anyhow!("bad file index");
                    bail!("verify space proofs error: {}", err);
                }
                let path_proof = PathProof {
                    locs: proof.proofs[i][j].locs.clone(),
                    path: proof.proofs[i][j].paths.clone(),
                };

                if !check_index_path(chals[j], &path_proof.locs) {
                    let err = anyhow!("verify index path error");
                    bail!("verify space proofs error: {}", err);
                }

                if !verify_path_proof(&proof.roots[i], &proof.proofs[i][j].label, path_proof) {
                    let err = anyhow!("verify path proof error");
                    bail!("verify space proofs error: {}", err);
                }
            }
            copy_data(
                &mut label,
                &[
                    &p_node.id,
                    &get_bytes(proof.left + i as i64),
                    &proof.roots[i],
                ],
            );

            if !get_hash(&label).eq(&proof.wit_chains[i].elem) {
                let err = anyhow!("verify file label error");
                bail!("verify space proofs error: {}", err);
            }
            //VerifyMutilevelAcc
            if !verify_mutilevel_acc(
                &p_node.record.as_ref().unwrap().key,
                &proof.wit_chains[i],
                &p_node.record.as_ref().unwrap().acc,
            ) {
                let err = anyhow!("verify acc proof error");
                bail!("verify space proofs error: {}", err);
            }
        }
        Ok(())
    }

    pub fn space_verification_handle<'a>(
        &'a mut self,
        id: &'a [u8],
        key: acc::RsaKey,
        acc: &'a [u8],
        front: i64,
        rear: i64,
    ) -> impl FnMut(&[i64], &SpaceProof) -> Result<bool> + 'a {
        let mut p_node = ProverNode::new(id, key, acc, front, rear);

        move |chals: &[i64], proof: &SpaceProof| -> Result<bool> {
            if let Err(_) = self.verify_space(&mut p_node, chals.to_vec(), proof) {
                return Ok(false);
            }
            p_node.record.as_mut().unwrap().record = proof.right - 1;
            if p_node.record.as_ref().unwrap().record == p_node.record.as_ref().unwrap().rear {
                Ok(true)
            } else {
                Ok(false)
            }
        }
    }

    pub fn verify_deletion(&mut self, id: &[u8], proof: &DeletionProof) -> Result<()> {
        let id_str = hex::encode(id);
        let p_node = self
            .nodes
            .get_mut(&id_str)
            .with_context(|| format!("Prover node not found"))?;

        if p_node.buf_size > 0 {
            let err = anyhow!("commit proof not finished");
            bail!("verify deletion proofs error: {}", err);
        }
        let lens = proof.roots.len();
        if lens
            > (p_node.record.as_ref().unwrap().rear - p_node.record.as_ref().unwrap().front)
                as usize
        {
            let err = anyhow!("file number out of range");
            bail!("verify deletion proofs error: {}", err);
        }
        let mut labels: Vec<Vec<u8>> = Vec::new();
        for i in 0..lens {
            let mut label: Vec<u8> = Vec::with_capacity(id.len() + 8 + HASH_SIZE as usize);
            copy_data(
                &mut label,
                &[
                    id,
                    &get_bytes(p_node.record.as_ref().unwrap().front + i as i64 + 1),
                    &proof.roots[i],
                ],
            );

            labels.push(get_hash(&label));
        }

        if verify_delete_update(
            p_node.record.as_ref().unwrap().key.clone(),
            &proof.wit_chain,
            labels,
            proof.acc_path.clone(),
            &p_node.record.as_ref().unwrap().acc,
        ) {
            let err = anyhow!("verify acc proof error");
            bail!("verify deletion proofs error: {}", err);
        }

        p_node.record.as_mut().unwrap().front += lens as i64;

        Ok(())
    }
}

impl ProverNode {
    pub fn new(id: &[u8], key: RsaKey, acc: &[u8], front: i64, rear: i64) -> Self {
        Self {
            id: id.to_vec(),
            commit_buf: Vec::<Commit>::with_capacity(MAX_BUF_SIZE as usize),
            buf_size: 0,
            record: Some(Record {
                acc: acc.to_vec(),
                front,
                rear,
                key,
                record: front,
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;

    #[test]
    fn test_receive_commits() {
        let mut verifier = Verifier::new(7, 512, 64);
        let key = acc::rsa_keygen(2048);
        let id = b"test miner id";

        // Register prover node with the verifier
        verifier.register_prover_node(id, key.clone(), key.g.to_string().as_bytes(), 0, 0);

        let mut commits = init_commit();

        // Commits received
        assert_eq!(verifier.receive_commits(id, &mut commits), true);
    }

    #[test]
    fn test_commit_challenges() {
        let mut verifier = Verifier::new(7, 512, 64);
        let key = acc::rsa_keygen(2048);
        let id = b"test miner id";

        // Register prover node with the verifier
        verifier.register_prover_node(id, key.clone(), key.g.to_string().as_bytes(), 0, 0);

        let mut commits = init_commit();

        if !verifier.receive_commits(id, &mut commits) {
            assert!(false);
        }

        let chals = verifier.commit_challenges(id, 0, 4);

        println!("{:?}", chals);
    }

    #[test]
    fn test_space_challenges() {
        let mut verifier = Verifier::new(7, 512, 64);
        let key = acc::rsa_keygen(2048);
        let id = b"test miner id";

        // Register prover node with the verifier
        verifier.register_prover_node(id, key.clone(), key.g.to_string().as_bytes(), 0, 0);

        let chals = verifier.space_challenges(22);

        println!("{:?}", chals);
    }

    fn init_commit() -> Vec<Commit> {
        vec![
            Commit {
                file_index: 1,
                roots: vec![
                    vec![
                        121, 162, 193, 172, 131, 126, 159, 48, 88, 75, 205, 99, 92, 127, 0, 67,
                        182, 10, 57, 59, 165, 158, 155, 154, 50, 245, 79, 198, 188, 75, 149, 42,
                        240, 235, 210, 88, 46, 87, 252, 219, 178, 87, 25, 169, 150, 245, 111, 9,
                        236, 202, 250, 117, 237, 137, 250, 174, 10, 53, 36, 186, 141, 185, 38, 72,
                    ],
                    vec![
                        253, 249, 38, 156, 39, 218, 16, 30, 250, 239, 181, 37, 146, 139, 79, 148,
                        60, 152, 117, 134, 86, 242, 72, 254, 183, 253, 252, 41, 237, 183, 200, 248,
                        142, 76, 248, 54, 106, 53, 194, 229, 35, 179, 19, 45, 12, 117, 121, 154,
                        184, 153, 116, 215, 140, 224, 148, 46, 207, 27, 57, 175, 192, 175, 144,
                        208,
                    ],
                    vec![
                        20, 89, 242, 210, 94, 5, 99, 173, 102, 192, 231, 103, 216, 27, 142, 76, 67,
                        75, 99, 85, 37, 202, 205, 45, 169, 85, 107, 6, 118, 134, 148, 133, 75, 167,
                        238, 136, 55, 236, 241, 252, 95, 186, 90, 174, 226, 142, 251, 116, 13, 174,
                        223, 5, 163, 50, 71, 27, 106, 195, 190, 9, 168, 97, 249, 226,
                    ],
                    vec![
                        35, 18, 62, 124, 92, 207, 158, 238, 178, 87, 216, 84, 99, 116, 215, 248,
                        246, 35, 47, 215, 181, 29, 76, 3, 123, 37, 171, 0, 188, 161, 178, 194, 121,
                        43, 178, 170, 21, 47, 126, 230, 187, 36, 137, 31, 210, 118, 176, 21, 237,
                        183, 243, 24, 113, 119, 7, 219, 89, 176, 69, 149, 48, 209, 153, 236,
                    ],
                    vec![
                        139, 17, 48, 193, 199, 128, 50, 68, 102, 212, 103, 144, 245, 142, 134, 28,
                        178, 2, 12, 115, 142, 125, 149, 186, 81, 102, 215, 179, 54, 129, 1, 154,
                        10, 65, 55, 214, 39, 36, 247, 65, 54, 123, 59, 221, 27, 108, 240, 112, 120,
                        189, 202, 239, 186, 121, 195, 154, 194, 223, 172, 220, 151, 96, 83, 137,
                    ],
                    vec![
                        33, 175, 7, 86, 99, 248, 38, 207, 157, 153, 185, 108, 43, 1, 33, 21, 89,
                        68, 156, 231, 132, 210, 113, 221, 218, 41, 15, 61, 207, 113, 209, 62, 243,
                        194, 179, 104, 224, 233, 17, 80, 248, 155, 73, 24, 54, 130, 44, 73, 202,
                        128, 209, 194, 150, 23, 12, 244, 221, 238, 107, 55, 41, 74, 15, 67,
                    ],
                    vec![
                        49, 94, 249, 194, 50, 189, 113, 198, 237, 207, 165, 27, 96, 83, 24, 123,
                        54, 121, 186, 124, 239, 203, 247, 238, 126, 24, 71, 83, 217, 143, 2, 85,
                        219, 34, 124, 241, 81, 250, 134, 92, 242, 127, 121, 233, 235, 172, 236,
                        101, 98, 73, 240, 49, 42, 224, 89, 178, 44, 237, 42, 129, 201, 195, 24,
                        114,
                    ],
                    vec![
                        135, 47, 95, 47, 34, 180, 178, 166, 188, 13, 212, 157, 39, 119, 52, 136,
                        198, 121, 70, 230, 241, 117, 188, 108, 163, 39, 214, 237, 214, 7, 96, 184,
                        254, 72, 37, 243, 168, 52, 236, 35, 170, 187, 25, 34, 41, 150, 252, 183,
                        53, 12, 66, 27, 182, 247, 20, 91, 189, 162, 177, 71, 200, 79, 244, 199,
                    ],
                    vec![
                        247, 251, 186, 241, 239, 161, 178, 170, 188, 8, 153, 214, 150, 154, 39, 85,
                        66, 65, 192, 128, 157, 169, 69, 23, 9, 25, 152, 186, 93, 22, 189, 222, 178,
                        204, 207, 188, 166, 59, 129, 36, 234, 180, 250, 101, 95, 236, 83, 181, 100,
                        6, 130, 212, 207, 194, 62, 64, 79, 81, 1, 90, 155, 30, 94, 207,
                    ],
                ],
            },
            Commit {
                file_index: 2,
                roots: vec![
                    vec![
                        193, 182, 183, 108, 113, 176, 54, 247, 68, 104, 37, 161, 22, 159, 132, 111,
                        160, 112, 246, 77, 240, 175, 90, 62, 168, 194, 92, 145, 191, 215, 253, 126,
                        215, 45, 56, 74, 149, 27, 83, 174, 59, 84, 101, 207, 216, 192, 245, 21,
                        143, 25, 108, 220, 100, 19, 87, 170, 233, 23, 107, 106, 109, 124, 151, 37,
                    ],
                    vec![
                        150, 178, 155, 192, 41, 106, 74, 152, 128, 237, 99, 216, 27, 12, 100, 167,
                        135, 137, 120, 7, 80, 117, 24, 115, 102, 148, 239, 157, 32, 207, 153, 247,
                        68, 135, 135, 223, 236, 59, 229, 2, 210, 198, 216, 65, 187, 35, 199, 52,
                        169, 196, 232, 8, 207, 163, 245, 208, 199, 225, 151, 13, 145, 253, 166,
                        166,
                    ],
                    vec![
                        25, 193, 152, 104, 229, 142, 140, 104, 6, 125, 218, 233, 133, 145, 221,
                        171, 183, 234, 181, 226, 109, 244, 203, 113, 225, 62, 87, 61, 109, 228, 58,
                        237, 0, 37, 230, 205, 235, 31, 224, 121, 170, 118, 152, 38, 162, 64, 176,
                        204, 182, 137, 248, 175, 61, 205, 237, 48, 50, 215, 101, 207, 96, 197, 228,
                        16,
                    ],
                    vec![
                        186, 182, 232, 29, 162, 88, 37, 110, 89, 36, 85, 90, 183, 99, 82, 23, 153,
                        9, 11, 42, 119, 169, 139, 126, 83, 7, 151, 123, 99, 176, 132, 51, 62, 1,
                        28, 220, 58, 93, 16, 9, 134, 118, 40, 171, 110, 184, 55, 141, 192, 207,
                        118, 200, 192, 216, 47, 95, 182, 131, 118, 237, 173, 54, 171, 82,
                    ],
                    vec![
                        69, 160, 217, 144, 228, 181, 72, 125, 175, 69, 73, 225, 176, 254, 59, 45,
                        140, 151, 161, 243, 98, 128, 134, 27, 186, 172, 154, 103, 72, 168, 9, 54,
                        138, 14, 103, 42, 110, 6, 46, 50, 229, 8, 177, 60, 26, 236, 35, 100, 159,
                        139, 255, 19, 102, 82, 52, 52, 199, 91, 168, 11, 233, 65, 61, 53,
                    ],
                    vec![
                        130, 166, 23, 102, 202, 185, 129, 189, 246, 217, 29, 49, 178, 125, 250,
                        132, 156, 115, 31, 117, 14, 163, 227, 22, 153, 246, 98, 228, 144, 10, 176,
                        195, 166, 178, 251, 129, 155, 132, 252, 162, 72, 90, 64, 50, 11, 153, 97,
                        53, 207, 183, 161, 118, 73, 19, 191, 183, 222, 53, 41, 35, 42, 20, 232,
                        191,
                    ],
                    vec![
                        98, 235, 150, 81, 192, 207, 220, 116, 251, 122, 198, 1, 68, 104, 154, 17,
                        21, 149, 128, 129, 147, 142, 218, 154, 195, 213, 43, 21, 26, 195, 115, 132,
                        3, 101, 24, 173, 176, 157, 243, 102, 253, 172, 70, 109, 124, 82, 116, 59,
                        151, 61, 164, 16, 173, 156, 203, 181, 161, 66, 38, 220, 117, 93, 206, 203,
                    ],
                    vec![
                        134, 69, 10, 158, 55, 60, 43, 19, 204, 35, 222, 225, 149, 78, 28, 15, 239,
                        121, 219, 231, 40, 231, 181, 42, 43, 255, 2, 242, 60, 114, 168, 6, 60, 21,
                        137, 61, 10, 107, 166, 0, 16, 173, 92, 17, 84, 56, 254, 234, 201, 143, 73,
                        69, 171, 234, 23, 50, 85, 242, 54, 135, 97, 23, 87, 33,
                    ],
                    vec![
                        97, 212, 83, 142, 109, 121, 230, 151, 212, 59, 191, 123, 60, 249, 57, 159,
                        55, 108, 110, 14, 150, 141, 72, 122, 123, 55, 63, 107, 191, 226, 157, 146,
                        23, 45, 26, 197, 239, 13, 175, 25, 210, 130, 206, 125, 61, 141, 125, 66,
                        218, 135, 231, 93, 63, 2, 49, 59, 108, 31, 48, 166, 120, 207, 230, 236,
                    ],
                ],
            },
            Commit {
                file_index: 3,
                roots: vec![
                    vec![
                        226, 14, 194, 165, 196, 34, 103, 34, 79, 87, 185, 233, 13, 54, 203, 57, 3,
                        128, 81, 35, 146, 185, 72, 119, 160, 61, 164, 7, 130, 57, 5, 72, 243, 75,
                        1, 159, 169, 136, 68, 90, 111, 44, 164, 26, 148, 172, 254, 113, 88, 240,
                        249, 194, 100, 249, 58, 164, 215, 203, 150, 85, 114, 172, 112, 81,
                    ],
                    vec![
                        62, 6, 115, 121, 0, 112, 186, 154, 69, 189, 146, 228, 115, 242, 88, 38,
                        243, 10, 74, 0, 53, 45, 108, 245, 113, 132, 252, 168, 127, 82, 196, 200,
                        244, 150, 228, 142, 245, 159, 115, 103, 219, 123, 68, 59, 29, 208, 254, 55,
                        14, 65, 204, 16, 110, 7, 145, 146, 172, 164, 168, 94, 234, 180, 46, 170,
                    ],
                    vec![
                        76, 230, 83, 49, 137, 203, 84, 171, 88, 0, 56, 66, 149, 116, 216, 233, 114,
                        76, 68, 22, 80, 136, 38, 163, 104, 115, 41, 203, 97, 135, 28, 60, 183, 10,
                        98, 153, 92, 221, 1, 176, 92, 120, 155, 217, 62, 153, 186, 64, 209, 86,
                        101, 149, 214, 21, 81, 93, 207, 226, 82, 153, 191, 208, 208, 25,
                    ],
                    vec![
                        205, 46, 139, 12, 162, 95, 227, 197, 101, 139, 138, 112, 0, 104, 65, 89,
                        61, 72, 192, 54, 236, 141, 75, 65, 118, 54, 191, 165, 15, 46, 121, 12, 102,
                        11, 214, 111, 162, 165, 161, 4, 184, 102, 100, 234, 247, 95, 212, 67, 217,
                        57, 74, 119, 110, 217, 29, 212, 222, 165, 234, 160, 19, 57, 179, 76,
                    ],
                    vec![
                        147, 24, 176, 70, 162, 159, 48, 31, 250, 218, 208, 182, 170, 44, 107, 54,
                        111, 82, 217, 113, 130, 227, 128, 68, 155, 223, 133, 121, 112, 119, 115,
                        171, 15, 10, 202, 228, 249, 106, 235, 236, 127, 187, 24, 236, 49, 178, 44,
                        164, 117, 66, 167, 181, 93, 160, 53, 9, 140, 198, 182, 252, 81, 239, 61,
                        137,
                    ],
                    vec![
                        94, 200, 11, 213, 219, 226, 182, 115, 250, 134, 229, 91, 74, 239, 69, 245,
                        215, 212, 56, 143, 140, 233, 33, 138, 117, 248, 13, 222, 56, 170, 57, 221,
                        243, 140, 85, 137, 193, 73, 101, 241, 99, 28, 246, 228, 239, 144, 235, 75,
                        14, 145, 215, 196, 21, 218, 117, 124, 94, 55, 134, 29, 223, 140, 131, 135,
                    ],
                    vec![
                        93, 155, 150, 26, 79, 233, 197, 98, 222, 45, 125, 3, 53, 168, 225, 174,
                        112, 84, 157, 141, 24, 218, 200, 219, 254, 96, 154, 174, 228, 12, 61, 243,
                        144, 85, 35, 0, 250, 33, 11, 77, 235, 138, 107, 0, 20, 171, 30, 79, 25,
                        169, 20, 121, 159, 189, 155, 143, 182, 238, 208, 196, 54, 138, 192, 106,
                    ],
                    vec![
                        105, 246, 24, 7, 144, 244, 51, 186, 164, 115, 54, 137, 48, 39, 3, 65, 243,
                        33, 38, 179, 45, 214, 125, 41, 74, 230, 132, 183, 114, 170, 68, 239, 87,
                        59, 225, 100, 87, 220, 89, 3, 194, 130, 181, 139, 104, 204, 235, 124, 116,
                        221, 29, 185, 136, 204, 204, 172, 249, 161, 199, 147, 178, 67, 217, 174,
                    ],
                    vec![
                        148, 238, 184, 112, 190, 229, 233, 123, 43, 35, 37, 146, 75, 68, 230, 210,
                        135, 193, 101, 187, 125, 176, 208, 123, 84, 46, 152, 171, 74, 180, 133,
                        192, 135, 42, 210, 208, 50, 222, 122, 89, 181, 71, 108, 31, 180, 225, 41,
                        190, 187, 41, 31, 115, 185, 17, 18, 129, 230, 230, 179, 28, 0, 159, 157,
                        231,
                    ],
                ],
            },
            Commit {
                file_index: 4,
                roots: vec![
                    vec![
                        140, 214, 205, 20, 172, 245, 37, 232, 211, 18, 118, 81, 153, 71, 163, 19,
                        218, 4, 250, 161, 71, 183, 29, 6, 23, 207, 157, 239, 143, 203, 141, 232,
                        234, 125, 34, 150, 181, 93, 148, 151, 157, 126, 62, 228, 139, 186, 251, 82,
                        175, 196, 91, 226, 0, 103, 136, 123, 251, 109, 106, 78, 189, 240, 99, 130,
                    ],
                    vec![
                        134, 230, 148, 135, 120, 160, 109, 226, 45, 134, 115, 153, 216, 28, 5, 175,
                        207, 223, 39, 77, 252, 224, 210, 40, 176, 202, 61, 201, 91, 145, 199, 113,
                        178, 6, 39, 239, 12, 178, 142, 155, 2, 181, 255, 58, 180, 49, 149, 142,
                        174, 47, 64, 43, 185, 88, 152, 206, 99, 178, 205, 36, 32, 77, 241, 151,
                    ],
                    vec![
                        241, 252, 28, 113, 69, 153, 159, 97, 50, 158, 25, 226, 100, 163, 64, 3, 81,
                        93, 22, 77, 162, 184, 78, 181, 231, 187, 228, 86, 182, 21, 202, 110, 130,
                        3, 0, 81, 166, 200, 41, 127, 161, 139, 43, 120, 60, 167, 212, 28, 87, 216,
                        112, 70, 231, 83, 138, 194, 220, 29, 247, 142, 44, 89, 79, 78,
                    ],
                    vec![
                        177, 139, 148, 15, 101, 201, 79, 71, 1, 131, 200, 95, 209, 111, 82, 130,
                        131, 251, 215, 147, 145, 131, 251, 135, 201, 70, 192, 93, 166, 226, 52, 88,
                        82, 205, 13, 133, 233, 62, 210, 106, 128, 255, 110, 148, 189, 188, 157, 96,
                        82, 132, 56, 119, 31, 24, 196, 222, 70, 217, 213, 25, 14, 248, 45, 226,
                    ],
                    vec![
                        163, 160, 248, 205, 166, 117, 114, 244, 116, 40, 13, 178, 115, 101, 88,
                        214, 194, 206, 151, 64, 194, 23, 190, 158, 121, 100, 175, 107, 141, 57,
                        101, 218, 96, 21, 181, 18, 207, 97, 5, 145, 16, 140, 37, 132, 130, 237, 82,
                        56, 197, 13, 129, 143, 147, 83, 89, 73, 103, 172, 234, 194, 227, 202, 156,
                        84,
                    ],
                    vec![
                        162, 156, 83, 8, 109, 136, 70, 57, 22, 133, 5, 104, 229, 120, 79, 33, 132,
                        116, 38, 27, 195, 59, 147, 96, 27, 228, 222, 29, 3, 142, 162, 120, 88, 195,
                        176, 32, 70, 245, 94, 243, 230, 177, 121, 206, 98, 17, 236, 105, 163, 235,
                        74, 213, 138, 8, 56, 103, 168, 182, 222, 165, 115, 96, 161, 115,
                    ],
                    vec![
                        15, 76, 96, 245, 186, 241, 156, 209, 234, 126, 134, 18, 242, 118, 243, 228,
                        112, 237, 69, 1, 51, 228, 218, 151, 107, 122, 252, 213, 124, 127, 138, 106,
                        28, 107, 209, 168, 113, 4, 25, 53, 176, 120, 116, 234, 150, 251, 88, 134,
                        163, 106, 228, 220, 129, 88, 131, 4, 123, 217, 33, 171, 41, 40, 131, 138,
                    ],
                    vec![
                        1, 171, 137, 194, 143, 4, 107, 174, 16, 205, 134, 156, 123, 128, 11, 97,
                        219, 170, 6, 132, 34, 158, 76, 221, 175, 56, 161, 132, 182, 153, 178, 52,
                        65, 192, 102, 172, 61, 34, 137, 206, 52, 41, 222, 99, 27, 176, 149, 110,
                        90, 44, 36, 162, 83, 206, 217, 174, 2, 225, 246, 19, 41, 248, 201, 50,
                    ],
                    vec![
                        71, 73, 144, 35, 36, 77, 242, 109, 0, 175, 14, 245, 218, 181, 186, 180,
                        115, 125, 207, 121, 51, 104, 210, 234, 150, 59, 77, 198, 120, 21, 114, 50,
                        132, 37, 6, 246, 189, 52, 96, 251, 168, 4, 233, 89, 217, 33, 41, 153, 50,
                        210, 150, 70, 175, 159, 167, 142, 101, 26, 38, 48, 199, 210, 84, 77,
                    ],
                ],
            },
        ]
    }
}
