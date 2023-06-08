use core::convert::TryInto;
use core::fmt;
use core::ops::{Add, Mul, Neg, Sub};
use ff::PrimeField;
use pasta_curves::arithmetic::{FieldExt, Group, SqrtRatio};
use rand::RngCore;
use serde::{Deserialize, Serialize};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::arithmetic::{adc, mac, sbb};
use crate::{
    field_common, impl_add_binop_specify_output, impl_binops_additive,
    impl_binops_additive_specify_output, impl_binops_multiplicative,
    impl_binops_multiplicative_mixed, impl_sub_binop_specify_output,
};
use crate::{impl_from_u64, maybe_u64::MaybeU64};

/// This represents an element of $\mathbb{F}_r$ where
///
/// `r = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001`
///
/// is the scalar field of the BN254 curve.
// The internal representation of this type is four 64-bit unsigned
// integers in little-endian order. `Fr` values are always in
// Montgomery form; i.e., Fr(a) = aR mod r, with R = 2^256.
#[derive(Clone, Debug, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Fr(MaybeU64);

/// Constant representing the modulus
/// r = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
pub const MODULUS_FULL: [u64; 4] = [
    0x43e1f593f0000001,
    0x2833e84879b97091,
    0xb85045b68181585d,
    0x30644e72e131a029,
];

pub const MODULUS: Fr = Fr(MaybeU64::Full(MODULUS_FULL));

const MODULUS_STR: &str = "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001";

/// INV = -(r^{-1} mod 2^64) mod 2^64
const INV: u64 = 0xc2e1f593efffffff;

/// `R = 2^256 mod r`
/// `0xe0a77c19a07df2f666ea36f7879462e36fc76959f60cd29ac96341c4ffffffb`
const R: Fr = Fr(MaybeU64::Full([
    0xac96341c4ffffffb,
    0x36fc76959f60cd29,
    0x666ea36f7879462e,
    0x0e0a77c19a07df2f,
]));

/// `R^2 = 2^512 mod r`
/// `0x216d0b17f4e44a58c49833d53bb808553fe3ab1e35c59e31bb8e645ae216da7`
const R2: Fr = Fr(MaybeU64::Full([
    0x1bb8e645ae216da7,
    0x53fe3ab1e35c59e3,
    0x8c49833d53bb8085,
    0x0216d0b17f4e44a5,
]));

/// `R^3 = 2^768 mod r`
/// `0xcf8594b7fcc657c893cc664a19fcfed2a489cbe1cfbb6b85e94d8e1b4bf0040`
const R3: Fr = Fr(MaybeU64::Full([
    0x5e94d8e1b4bf0040,
    0x2a489cbe1cfbb6b8,
    0x893cc664a19fcfed,
    0x0cf8594b7fcc657c,
]));

/// `GENERATOR = 7 mod r` is a generator of the `r - 1` order multiplicative
/// subgroup, or in other words a primitive root of the field.
const GENERATOR: Fr = Fr(MaybeU64::U64(7));

const S: u32 = 28;

/// GENERATOR^t where t * 2^s + 1 = r
/// with t odd. In other words, this
/// is a 2^s root of unity.
/// `0x3ddb9f5166d18b798865ea93dd31f743215cf6dd39329c8d34f1ed960c37c9c`
const ROOT_OF_UNITY: Fr = Fr::from_raw([
    0xd34f1ed960c37c9c,
    0x3215cf6dd39329c8,
    0x98865ea93dd31f74,
    0x03ddb9f5166d18b7,
]);

/// 1 / 2 mod r
const TWO_INV: Fr = Fr::from_raw([
    0xa1f0fac9f8000001,
    0x9419f4243cdcb848,
    0xdc2822db40c0ac2e,
    0x183227397098d014,
]);

/// 1 / ROOT_OF_UNITY mod r
const ROOT_OF_UNITY_INV: Fr = Fr::from_raw([
    0x0ed3e50a414e6dba,
    0xb22625f59115aba7,
    0x1bbe587180f34361,
    0x048127174daabc26,
]);

/// GENERATOR^{2^s} where t * 2^s + 1 = r
/// with t odd. In other words, this
/// is a t root of unity.
// 0x09226b6e22c6f0ca64ec26aad4c86e715b5f898e5e963f25870e56bbe533e9a2
const DELTA: Fr = Fr::from_raw([
    0x870e56bbe533e9a2,
    0x5b5f898e5e963f25,
    0x64ec26aad4c86e71,
    0x09226b6e22c6f0ca,
]);

/// `ZETA^3 = 1 mod r` where `ZETA^2 != 1 mod r`
const ZETA: Fr = Fr::from_raw([
    0xb8ca0b2d36636f23,
    0xcc37a73fec2bc5e9,
    0x048b6e193fd84104,
    0x30644e72e131a029,
]);

impl Fr {
    pub fn to_full(&mut self) {
        match self.0 {
            MaybeU64::Full(p) => panic!("{} is already a full element", p),
            MaybeU64::U64(p) => {
                // todo: integrate the lookup table
                Fr::from_raw([p, 0, 0, 0])
            }
        }
    }
}

impl Default for Fr {
    fn default() -> Self {
        Self(MaybeU64::U64(0))
    }
}

impl ConditionallySelectable for Fr {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        // warning: NOT constant time
        if choice.unwrap_u8() as bool {
            a
        } else {
            b
        }
    }
}

impl ConstantTimeEq for Fr {
    fn ct_eq(&self, other: &Self) -> Choice {
        // warning: NOT constant time
        match self.0 {
            MaybeU64::Full(s) => match other.0 {
                MaybeU64::Full(other) => {
                    self.0[0].ct_eq(&other.0[0])
                        & self.0[1].ct_eq(&other.0[1])
                        & self.0[2].ct_eq(&other.0[2])
                        & self.0[3].ct_eq(&other.0[3])
                }
                MaybeU64::U64(other) => Choice::from(false),
            },
            MaybeU64::U64(s) => match other.0 {
                MaybeU64::Full(other) => Choice::from(false),
                MaybeU64::U64(other) => s.ct_eq(&other),
            },
        }
    }
}

/// Adds `rhs` to `self`, returning the result.
#[inline]
pub const fn add(lhs: &[u64; 4], rhs: &[u64; 4]) -> [u64; 4] {
    let (d0, carry) = adc(lhs[0], rhs[0], 0);
    let (d1, carry) = adc(lhs[1], rhs[1], carry);
    let (d2, carry) = adc(lhs[2], rhs[2], carry);
    let (d3, _) = adc(lhs[3], rhs[3], carry);

    // Attempt to subtract the modulus, to ensure the value
    // is smaller than the modulus.
    sub(&[d0, d1, d2, d3], &MODULUS_FULL)
}

#[inline]
pub const fn sub(lhs: &[u64; 4], rhs: &[u64; 4]) -> [u64; 4] {
    let (d0, borrow) = sbb(lhs[0], rhs[0], 0);
    let (d1, borrow) = sbb(lhs[1], rhs[1], borrow);
    let (d2, borrow) = sbb(lhs[2], rhs[2], borrow);
    let (d3, borrow) = sbb(lhs[3], rhs[3], borrow);

    // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
    // borrow = 0x000..000. Thus, we use it as a mask to conditionally add the modulus.
    let (d0, carry) = adc(d0, MODULUS_FULL[0] & borrow, 0);
    let (d1, carry) = adc(d1, MODULUS_FULL[1] & borrow, carry);
    let (d2, carry) = adc(d2, MODULUS_FULL[2] & borrow, carry);
    let (d3, _) = adc(d3, MODULUS_FULL[3] & borrow, carry);

    [d0, d1, d2, d3]
}

impl Add for Fr {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match self.0 {
            MaybeU64::Full(s) => match rhs.0 {
                MaybeU64::Full(other) => Fr(MaybeU64::Full(add(&s, &other))),
                MaybeU64::U64(other) => Fr(MaybeU64::Full(add(&s, &rhs.to_full().0))),
            },
            MaybeU64::U64(s) => match rhs.0 {
                MaybeU64::Full(other) => {
                    let (res, carry) = adc(s, other, 0);
                    if carry {
                        self.to_full() + rhs.to_full()
                    } else {
                        Fr(MaybeU64::U64(res))
                    }
                }
                MaybeU64::U64(other) => Fr(MaybeU64::Full(add(&s, &rhs.to_full().0))),
            },
        }
    }
}

// impl ff::Field for Fr {
//     fn random(mut rng: impl RngCore) -> Self {
//         Self::from_u512([
//             rng.next_u64(),
//             rng.next_u64(),
//             rng.next_u64(),
//             rng.next_u64(),
//             rng.next_u64(),
//             rng.next_u64(),
//             rng.next_u64(),
//             rng.next_u64(),
//         ])
//     }

//     fn zero() -> Self {
//         Self::zero()
//     }

//     fn one() -> Self {
//         Self::one()
//     }

//     fn double(&self) -> Self {
//         self.double()
//     }

//     #[inline(always)]
//     fn square(&self) -> Self {
//         self.square()
//     }

//     /// Computes the square root of this element, if it exists.
//     fn sqrt(&self) -> CtOption<Self> {
//         crate::arithmetic::sqrt_tonelli_shanks(self, &<Self as SqrtRatio>::T_MINUS1_OVER2)
//     }

//     /// Computes the multiplicative inverse of this element,
//     /// failing if the element is zero.
//     fn invert(&self) -> CtOption<Self> {
//         let tmp = self.pow(&[
//             0x43e1f593efffffff,
//             0x2833e84879b97091,
//             0xb85045b68181585d,
//             0x30644e72e131a029,
//         ]);

//         CtOption::new(tmp, !self.ct_eq(&Self::zero()))
//     }
// }

// impl From<u64> for Fr {
//     fn from(data: u64) -> Self {
//         Self(MaybeU64::U64(data))
//     }
// }

// impl PrimeField for Fr {
//     type Repr = [u8; 32];

//     const NUM_BITS: u32 = 254;
//     const CAPACITY: u32 = 253;
//     const S: u32 = S;

//     fn from_repr(repr: Self::Repr) -> CtOption<Self> {
//         let mut tmp = [0, 0, 0, 0];

//         tmp[0] = u64::from_le_bytes(repr[0..8].try_into().unwrap());
//         tmp[1] = u64::from_le_bytes(repr[8..16].try_into().unwrap());
//         tmp[2] = u64::from_le_bytes(repr[16..24].try_into().unwrap());
//         tmp[3] = u64::from_le_bytes(repr[24..32].try_into().unwrap());

//         // Try to subtract the modulus
//         let (_, borrow) = sbb(tmp[0], MODULUS_FULL[0], 0);
//         let (_, borrow) = sbb(tmp[1], MODULUS_FULL[1], borrow);
//         let (_, borrow) = sbb(tmp[2], MODULUS_FULL[2], borrow);
//         let (_, borrow) = sbb(tmp[3], MODULUS_FULL[3], borrow);

//         // If the element is smaller than MODULUS then the
//         // subtraction will underflow, producing a borrow value
//         // of 0xffff...ffff. Otherwise, it'll be zero.
//         let is_some = (borrow as u8) & 1;

//         // Convert to Montgomery form by computing
//         // (a.R^0 * R^2) / R = a.R
//         let mut tmp = Fr(MaybeU64::Full(tmp));
//         tmp *= &R2;

//         CtOption::new(tmp, Choice::from(is_some))
//     }

//     fn to_repr(&self) -> Self::Repr {
//         match self.0 {
//             MaybeU64::Full(repr) => {
//                 // Turn into canonical form by computing
//                 // (a.R) / R = a
//                 let tmp = Fr::montgomery_reduce(&[repr[0], repr[1], repr[2], repr[3], 0, 0, 0, 0]);

//                 let mut res = [0; 32];
//                 res[0..8].copy_from_slice(&tmp.0[0].to_le_bytes());
//                 res[8..16].copy_from_slice(&tmp.0[1].to_le_bytes());
//                 res[16..24].copy_from_slice(&tmp.0[2].to_le_bytes());
//                 res[24..32].copy_from_slice(&tmp.0[3].to_le_bytes());

//                 res
//             }
//             MaybeU64::U64(repr) => repr
//                 .to_le_bytes()
//                 .iter()
//                 .chain([0u8; 24].iter())
//                 .cloned()
//                 .collect::<Vec<_>>()
//                 .try_into()
//                 .unwrap(),
//         }
//     }

//     fn is_odd(&self) -> Choice {
//         Choice::from(self.to_repr()[0] & 1)
//     }

//     fn multiplicative_generator() -> Self {
//         GENERATOR
//     }

//     fn root_of_unity() -> Self {
//         ROOT_OF_UNITY
//     }
// }

// impl SqrtRatio for Fr {
//     /// `(t - 1) // 2` where t * 2^s + 1 = p with t odd.
//     const T_MINUS1_OVER2: [u64; 4] = [
//         0xcdcb848a1f0fac9f,
//         0x0c0ac2e9419f4243,
//         0x098d014dc2822db4,
//         0x0000000183227397,
//     ];

//     fn get_lower_32(&self) -> u32 {
//         match self.0 {
//             MaybeU64::Full(repr) => {
//                 let tmp = Fr::montgomery_reduce(&[repr[0], repr[1], repr[2], repr[3], 0, 0, 0, 0]);
//                 tmp.0[0] as u32
//             }
//             MaybeU64::U64(repr) => repr as u32,
//         }
//     }
// }
