use std::{
    ops::{Div, Mul, Shl},
    str::FromStr,
};

use bigdecimal::BigDecimal;
use num_bigint_dig::{prime::probably_prime, BigUint};
use num_traits::{FromPrimitive, One, ToPrimitive};

fn fu(x: &BigUint) -> BigUint {
    let u = x.clone();
    let one = BigUint::one();

    let two = BigUint::from(2u32);

    let mut temp1: BigUint = &u + &two;
    temp1 *= &two;
    let temp2 = &u + &one;
    let bit = temp2.bits();
    let divisor = one.shl(bit - 1);

    let f = BigDecimal::from_str(&temp2.to_string()).unwrap();
    let z = f.div(BigDecimal::from_str(divisor.to_string().as_str()).unwrap());
    let w = z.to_f64().unwrap();
    let y = (f64::log2(w) + (bit - 1) as f64).powi(2);
    let y = BigUint::from_f64(y).unwrap();
    let temp1 = &temp1.mul(&y);

    temp1.clone()
}

pub fn h_prime(u: &BigUint) -> BigUint {
    let mut j = fu(u);
    let temp = fu(u);
    loop {
        let prime = &temp + &j;
        if probably_prime(&prime, 10) {
            return prime;
        }
        j += BigUint::from_u32(1u32).unwrap();
    }
}
