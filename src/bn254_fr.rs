#[cfg(feature = "asm")]
use super::assembly::field_arithmetic_asm;
#[cfg(not(feature = "asm"))]
use crate::{field_arithmetic, field_specific};

use crate::arithmetic::{adc, mac, sbb};
use core::convert::TryInto;
use core::fmt;
use core::ops::{Add, Mul, Neg, Sub};
use ff::PrimeField;
// use pasta_curves::arithmetic::{FieldExt, Group, SqrtRatio};
use rand::RngCore;
use serde::{Deserialize, Serialize};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

/// This represents an element of $\mathbb{F}_r$ where
///
/// `r = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001`
///
/// is the scalar field of the BN254 curve.
// The internal representation of this type is four 64-bit unsigned
// integers in little-endian order. `Fr` values are always in
// Montgomery form; i.e., Fr(a) = aR mod r, with R = 2^256.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FrInteral(pub(crate) [u64; 4]);

/// Constant representing the modulus
/// r = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
pub const MODULUS: FrInteral = FrInteral([
    0x43e1f593f0000001,
    0x2833e84879b97091,
    0xb85045b68181585d,
    0x30644e72e131a029,
]);

const MODULUS_STR: &str = "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001";

/// INV = -(r^{-1} mod 2^64) mod 2^64
const INV: u64 = 0xc2e1f593efffffff;

/// `R = 2^256 mod r`
/// `0xe0a77c19a07df2f666ea36f7879462e36fc76959f60cd29ac96341c4ffffffb`
pub(crate) const R: FrInteral = FrInteral([
    0xac96341c4ffffffb,
    0x36fc76959f60cd29,
    0x666ea36f7879462e,
    0x0e0a77c19a07df2f,
]);

/// `R^2 = 2^512 mod r`
/// `0x216d0b17f4e44a58c49833d53bb808553fe3ab1e35c59e31bb8e645ae216da7`
const R2: FrInteral = FrInteral([
    0x1bb8e645ae216da7,
    0x53fe3ab1e35c59e3,
    0x8c49833d53bb8085,
    0x0216d0b17f4e44a5,
]);

/// `R^3 = 2^768 mod r`
/// `0xcf8594b7fcc657c893cc664a19fcfed2a489cbe1cfbb6b85e94d8e1b4bf0040`
const R3: FrInteral = FrInteral([
    0x5e94d8e1b4bf0040,
    0x2a489cbe1cfbb6b8,
    0x893cc664a19fcfed,
    0x0cf8594b7fcc657c,
]);

/// `GENERATOR = 7 mod r` is a generator of the `r - 1` order multiplicative
/// subgroup, or in other words a primitive root of the field.
const GENERATOR: FrInteral = FrInteral::from_raw([0x07, 0x00, 0x00, 0x00]);

const S: u32 = 28;

/// GENERATOR^t where t * 2^s + 1 = r
/// with t odd. In other words, this
/// is a 2^s root of unity.
/// `0x3ddb9f5166d18b798865ea93dd31f743215cf6dd39329c8d34f1ed960c37c9c`
const ROOT_OF_UNITY: FrInteral = FrInteral::from_raw([
    0xd34f1ed960c37c9c,
    0x3215cf6dd39329c8,
    0x98865ea93dd31f74,
    0x03ddb9f5166d18b7,
]);

/// 1 / 2 mod r
const TWO_INV: FrInteral = FrInteral::from_raw([
    0xa1f0fac9f8000001,
    0x9419f4243cdcb848,
    0xdc2822db40c0ac2e,
    0x183227397098d014,
]);

/// 1 / ROOT_OF_UNITY mod r
const ROOT_OF_UNITY_INV: FrInteral = FrInteral::from_raw([
    0x0ed3e50a414e6dba,
    0xb22625f59115aba7,
    0x1bbe587180f34361,
    0x048127174daabc26,
]);

/// GENERATOR^{2^s} where t * 2^s + 1 = r
/// with t odd. In other words, this
/// is a t root of unity.
// 0x09226b6e22c6f0ca64ec26aad4c86e715b5f898e5e963f25870e56bbe533e9a2
const DELTA: FrInteral = FrInteral::from_raw([
    0x870e56bbe533e9a2,
    0x5b5f898e5e963f25,
    0x64ec26aad4c86e71,
    0x09226b6e22c6f0ca,
]);

/// `ZETA^3 = 1 mod r` where `ZETA^2 != 1 mod r`
const ZETA: FrInteral = FrInteral::from_raw([
    0xb8ca0b2d36636f23,
    0xcc37a73fec2bc5e9,
    0x048b6e193fd84104,
    0x30644e72e131a029,
]);

#[cfg(not(feature = "bn256-table"))]
use crate::impl_from_u64;
use crate::{
    field_common, impl_add_binop_specify_output, impl_binops_additive,
    impl_binops_additive_specify_output, impl_binops_multiplicative,
    impl_binops_multiplicative_mixed, impl_sub_binop_specify_output,
};

impl_binops_additive!(FrInteral, FrInteral);
impl_binops_multiplicative!(FrInteral, FrInteral);
field_common!(
    FrInteral,
    MODULUS,
    INV,
    MODULUS_STR,
    TWO_INV,
    ROOT_OF_UNITY_INV,
    DELTA,
    ZETA,
    R,
    R2,
    R3
);

impl_from_u64!(FrInteral, R2);

#[cfg(not(feature = "asm"))]
field_arithmetic!(FrInteral, MODULUS, INV, sparse);
#[cfg(feature = "asm")]
field_arithmetic_asm!(FrInteral, MODULUS, INV);

impl ff::Field for FrInteral {

    const ONE: Self = F;

    fn random(mut rng: impl RngCore) -> Self {
        Self::from_u512([
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
        ])
    }


    fn double(&self) -> Self {
        self.double()
    }

    #[inline(always)]
    fn square(&self) -> Self {
        self.square()
    }

    /// Computes the square root of this element, if it exists.
    fn sqrt(&self) -> CtOption<Self> {
        crate::arithmetic::sqrt_tonelli_shanks(self, &<Self as SqrtRatio>::T_MINUS1_OVER2)
    }

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    fn invert(&self) -> CtOption<Self> {
        let tmp = self.pow(&[
            0x43e1f593efffffff,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ]);

        CtOption::new(tmp, !self.ct_eq(&Self::zero()))
    }
}

impl ff::PrimeField for FrInteral {
    type Repr = [u8; 32];

    const NUM_BITS: u32 = 254;
    const CAPACITY: u32 = 253;
    const S: u32 = S;

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let mut tmp = FrInteral([0, 0, 0, 0]);

        tmp.0[0] = u64::from_le_bytes(repr[0..8].try_into().unwrap());
        tmp.0[1] = u64::from_le_bytes(repr[8..16].try_into().unwrap());
        tmp.0[2] = u64::from_le_bytes(repr[16..24].try_into().unwrap());
        tmp.0[3] = u64::from_le_bytes(repr[24..32].try_into().unwrap());

        // Try to subtract the modulus
        let (_, borrow) = sbb(tmp.0[0], MODULUS.0[0], 0);
        let (_, borrow) = sbb(tmp.0[1], MODULUS.0[1], borrow);
        let (_, borrow) = sbb(tmp.0[2], MODULUS.0[2], borrow);
        let (_, borrow) = sbb(tmp.0[3], MODULUS.0[3], borrow);

        // If the element is smaller than MODULUS then the
        // subtraction will underflow, producing a borrow value
        // of 0xffff...ffff. Otherwise, it'll be zero.
        let is_some = (borrow as u8) & 1;

        // Convert to Montgomery form by computing
        // (a.R^0 * R^2) / R = a.R
        tmp *= &R2;

        CtOption::new(tmp, Choice::from(is_some))
    }

    fn to_repr(&self) -> Self::Repr {
        // Turn into canonical form by computing
        // (a.R) / R = a
        let tmp =
            FrInteral::montgomery_reduce(&[self.0[0], self.0[1], self.0[2], self.0[3], 0, 0, 0, 0]);

        let mut res = [0; 32];
        res[0..8].copy_from_slice(&tmp.0[0].to_le_bytes());
        res[8..16].copy_from_slice(&tmp.0[1].to_le_bytes());
        res[16..24].copy_from_slice(&tmp.0[2].to_le_bytes());
        res[24..32].copy_from_slice(&tmp.0[3].to_le_bytes());

        res
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.to_repr()[0] & 1)
    }

    fn multiplicative_generator() -> Self {
        GENERATOR
    }

    fn root_of_unity() -> Self {
        ROOT_OF_UNITY
    }
}

impl SqrtRatio for FrInteral {
    /// `(t - 1) // 2` where t * 2^s + 1 = p with t odd.
    const T_MINUS1_OVER2: [u64; 4] = [
        0xcdcb848a1f0fac9f,
        0x0c0ac2e9419f4243,
        0x098d014dc2822db4,
        0x0000000183227397,
    ];

    fn get_lower_32(&self) -> u32 {
        let tmp =
            FrInteral::montgomery_reduce(&[self.0[0], self.0[1], self.0[2], self.0[3], 0, 0, 0, 0]);
        tmp.0[0] as u32
    }
}

#[cfg(test)]
mod test {
    use crate::serde::SerdeObject;

    use super::*;
    use ark_std::{end_timer, start_timer};
    use ff::Field;
    use rand::SeedableRng;
    use rand_core::OsRng;
    use rand_xorshift::XorShiftRng;

    #[test]
    fn test_sqrt() {
        let v = (FrInteral::TWO_INV).square().sqrt().unwrap();
        assert!(v == FrInteral::TWO_INV || (-v) == FrInteral::TWO_INV);

        for _ in 0..10000 {
            let a = FrInteral::random(OsRng);
            let mut b = a;
            b = b.square();

            let b = b.sqrt().unwrap();
            let mut negb = b;
            negb = negb.neg();

            assert!(a == b || a == negb);
        }
    }

    #[test]
    fn test_root_of_unity() {
        assert_eq!(
            FrInteral::root_of_unity().pow_vartime(&[1 << FrInteral::S, 0, 0, 0]),
            FrInteral::one()
        );
    }

    #[test]
    fn test_inv_root_of_unity() {
        assert_eq!(
            FrInteral::ROOT_OF_UNITY_INV,
            FrInteral::root_of_unity().invert().unwrap()
        );
    }

    #[test]
    fn test_field() {
        crate::tests::field::random_field_tests::<FrInteral>("bn256 scalar".to_string());
    }

    #[test]
    fn test_delta() {
        assert_eq!(
            FrInteral::DELTA,
            GENERATOR.pow(&[1u64 << FrInteral::S, 0, 0, 0])
        );
        assert_eq!(
            FrInteral::DELTA,
            FrInteral::multiplicative_generator().pow(&[1u64 << FrInteral::S, 0, 0, 0])
        );
    }

    #[test]
    fn test_from_u512() {
        assert_eq!(
            FrInteral::from_raw([
                0x7e7140b5196b9e6f,
                0x9abac9e4157b6172,
                0xf04bc41062fd7322,
                0x1185fa9c9fef6326,
            ]),
            FrInteral::from_u512([
                0xaaaaaaaaaaaaaaaa,
                0xaaaaaaaaaaaaaaaa,
                0xaaaaaaaaaaaaaaaa,
                0xaaaaaaaaaaaaaaaa,
                0xaaaaaaaaaaaaaaaa,
                0xaaaaaaaaaaaaaaaa,
                0xaaaaaaaaaaaaaaaa,
                0xaaaaaaaaaaaaaaaa
            ])
        );
    }

    #[test]
    fn test_serialization() {
        crate::tests::field::random_serialization_test::<FrInteral>("fr".to_string());
    }

    fn is_less_than(x: &[u64; 4], y: &[u64; 4]) -> bool {
        match x[3].cmp(&y[3]) {
            core::cmp::Ordering::Less => return true,
            core::cmp::Ordering::Greater => return false,
            _ => {}
        }
        match x[2].cmp(&y[2]) {
            core::cmp::Ordering::Less => return true,
            core::cmp::Ordering::Greater => return false,
            _ => {}
        }
        match x[1].cmp(&y[1]) {
            core::cmp::Ordering::Less => return true,
            core::cmp::Ordering::Greater => return false,
            _ => {}
        }
        x[0].lt(&y[0])
    }

    #[test]
    fn test_serialization_check() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        let start = start_timer!(|| "serialize fr");
        // failure check
        for _ in 0..1000000 {
            let rand_word = [(); 4].map(|_| rng.next_u64());
            let a = FrInteral(rand_word);
            let rand_bytes = a.to_raw_bytes();
            match is_less_than(&rand_word, &MODULUS.0) {
                false => {
                    assert!(FrInteral::from_raw_bytes(&rand_bytes).is_none());
                }
                _ => {
                    assert_eq!(FrInteral::from_raw_bytes(&rand_bytes), Some(a));
                }
            }
        }
        end_timer!(start);
    }

    #[test]
    fn bench_fr_from_u16() {
        let repeat = 10000000;
        let mut rng = ark_std::test_rng();
        let base = (0..repeat).map(|_| (rng.next_u32() % (1 << 16)) as u64);

        let timer = start_timer!(|| format!("generate {} Bn256 scalar field elements", repeat));
        let _res: Vec<_> = base.map(|b| FrInteral::from(b)).collect();

        end_timer!(timer);
    }
}
