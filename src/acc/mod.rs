pub mod hash_2_prime;
pub mod multi_level_acc;

use num_bigint_dig::{BigUint, RandBigInt};
use num_integer::Integer;
use num_traits::{One, Zero};
use rsa::{traits::PublicKeyParts, RsaPrivateKey};

use self::{hash_2_prime::h_prime, multi_level_acc::WitnessNode};

#[derive(Clone, Debug)]
pub struct RsaKey {
    pub n: BigUint, //Z/nZ
    pub g: BigUint, // Generator
}

pub fn rsa_keygen(lambda: usize) -> RsaKey {
    let mut rng = rand::thread_rng();
    let pk = RsaPrivateKey::new(&mut rng, lambda).expect("Failed to generate RSA key");

    let n = pk.n();
    let mut f: BigUint;
    let g: BigUint;

    loop {
        f = rng.gen_biguint(lambda);
        if f.gcd(n) == BigUint::one() {
            break;
        }
    }
    g = f.modpow(&BigUint::from(2u32), &n.clone());

    RsaKey {
        n: n.clone(),
        g: g.clone(),
    }
}

pub fn generate_acc(key: &RsaKey, acc: &[u8], elems: Vec<Vec<u8>>) -> Option<Vec<u8>> {
    if acc.is_empty() {
        return None;
    }

    let mut g = BigUint::from_bytes_be(acc);
    for elem in elems {
        let prime = h_prime(&BigUint::from_bytes_be(&elem));
        g = g.modpow(&prime, &key.n);
    }

    Some(g.to_bytes_be())
}
