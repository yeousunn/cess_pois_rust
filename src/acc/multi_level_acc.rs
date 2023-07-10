use num_bigint_dig::BigUint;
use serde::{Deserialize, Serialize};

use super::{generate_acc, hash_2_prime::h_prime, RsaKey};

const DEFAULT_PATH: &str = "./acc/";
const DEFAULT_DIR_PERM: i32 = 0777;
const DEFAULT_ELEMS_NUM: i32 = 1024;
const DEFAULT_LEVEL: i32 = 3;
const DEFAULT_NAME: &str = "sub-acc";
const DEFAULT_BACKUP_NAME: &str = "backup-sub-acc";

#[derive(Clone, Deserialize, Serialize)]
pub struct WitnessNode {
    pub elem: Vec<u8>,
    pub wit: Vec<u8>,
    pub acc: Option<Box<WitnessNode>>,
}

pub fn verify_insert_update(
    key: RsaKey,
    exist: &mut WitnessNode,
    elems: Vec<Vec<u8>>,
    accs: Vec<Vec<u8>>,
    acc: Vec<u8>,
) -> bool {
    if elems.is_empty() || accs.len() < DEFAULT_LEVEL as usize {
        return false;
    }

    let mut p = exist.clone();
    // If the condition is true, a new accumulator is inserted
    while p.acc.as_ref().unwrap().acc.is_some() && p.acc.as_ref().unwrap().elem == p.wit {
        p = *p.acc.unwrap().clone();
    }

    // Proof of the witness of accumulator elements,
    // when the element's accumulator does not exist, recursively verify its parent accumulator
    if !verify_mutilevel_acc(&key, &mut p.clone(), &acc.clone()) {
        return false;
    }

    // Verify that the newly generated accumulators after inserting elements
    // is calculated based on the original accumulators
    let sub_acc = generate_acc(&key.clone(), &p.elem, elems.clone());
    if !sub_acc.eq(&Some(accs[0].clone())) {
        return false;
    }

    let mut count = 1;
    let mut p = exist.clone();
    while let Some(p_node) = Some(p.clone()) {
        let sub_acc = generate_acc(&key.clone(), &p_node.wit.clone(), vec![accs[count - 1].clone()]);
        if sub_acc != Some(accs[count].clone()) {
            return false;
        }
        p = *p_node.acc.unwrap().clone();
        count += 1;
    }

    true
}

fn verify_acc(key: &RsaKey, acc: &[u8], u: &[u8], wit: &[u8]) -> bool {
    let e = h_prime(&BigUint::from_bytes_be(u));
    let dash = BigUint::from_bytes_be(wit).modpow(&e, &key.n);
    dash == BigUint::from_bytes_be(acc)
}

pub fn verify_mutilevel_acc(key: &RsaKey, wits: &WitnessNode, acc: &[u8]) -> bool {
    let mut current_wit = wits;

    while let Some(acc_node) = &current_wit.acc {
        if !verify_acc(key, &acc_node.elem, &current_wit.elem, &current_wit.wit) {
            return false;
        }
        current_wit = acc_node;
    }

    current_wit.elem == acc
}

pub fn verify_delete_update(
    key: RsaKey,
    exist: &WitnessNode,
    elems: Vec<Vec<u8>>,
    accs: Vec<Vec<u8>>,
    acc: &[u8],
) -> bool {
    if elems.len() == 0 || accs.len() < DEFAULT_LEVEL as usize {
        return false;
    }
    if !verify_mutilevel_acc(&key, exist, acc) {
        return false;
    }

    let mut sub_acc = generate_acc(&key, &accs[0], elems);
    if sub_acc.eq(&Some(exist.elem.clone())) {
        return false;
    }
    let mut p = exist;
    let mut count = 1;
    while !p.acc.is_none() {
        if accs[count - 1].eq(&key.g.to_bytes_be()) {
            sub_acc = generate_acc(&key, &p.wit, vec![accs[count - 1].clone()]);
        } else {
            sub_acc = Some(p.wit.clone());
        }
        if sub_acc.eq(&Some(accs[count].to_vec())) {
            return false;
        }
        p = &p.acc.as_ref().unwrap();
        count += 1;
    }

    return true;
}
