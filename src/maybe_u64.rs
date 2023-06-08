use std::ops::Add;

use ff::{Field, PrimeField};
use rand_core::RngCore;
use serde::{Deserialize, Serialize};

use crate::bn254_fr::R;
use crate::impl_add_binop_specify_output;
use crate::{arithmetic::adc, bn254_fr::FrInteral};

// mod field_ops;
// mod util;

mod add;
mod sub;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
/// Struct for a 256-bits field elements.
/// - U64: if the element is less than 1<<64
/// - Full: otherwise
///
/// This allows for faster computation with u64 ops.
pub enum MaybeU64<F> {
    U64(u64),
    Full(F),
}

pub trait MaybeU64Coversion {
    /// Convert a u64 to a full field element
    fn to_full(&self) -> Self;
    /// Convert a full field element into u64 format.
    fn to_u64(&self) -> Self;
    /// random u64
    fn random_u64(rng: impl RngCore) -> Self;
    /// random field element
    fn random_field(rng: impl RngCore) -> Self;
}

impl<F> MaybeU64Coversion for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    /// Convert a u64 to a full field element
    fn to_full(&self) -> Self {
        match *self {
            MaybeU64::Full(p) => panic!("{:?} is already a full element", p),
            MaybeU64::U64(p) => Self::Full(F::from(p)),
        }
    }

    /// Convert a full field element into u64 format.
    fn to_u64(&self) -> Self {
        match *self {
            MaybeU64::Full(p) => {
                let repr = p.to_repr();
                for e in repr.iter().skip(8) {
                    assert_eq!(*e, 0, "{:?} is not an u64", p)
                }
                MaybeU64::U64(u64::from_le_bytes(repr[0..8].try_into().unwrap()))
            }
            MaybeU64::U64(p) => panic!("{} is already a u64", p),
        }
    }

    /// random u64
    fn random_u64(mut rng: impl RngCore) -> Self {
        Self::U64(rng.next_u64())
    }

    /// random field element
    fn random_field(rng: impl RngCore) -> Self {
        Self::Full(F::random(rng))
    }
}

impl<F: Field> From<u64> for MaybeU64<F> {
    fn from(value: u64) -> Self {
        Self::U64(value)
    }
}

// impl<F: Field> Field for MaybeU64<F> {
//     fn random(rng: impl RngCore) -> Self {
//         Self::Full(FrInteral::random(rng))
//     }
// }

#[cfg(test)]
mod test {
    use ark_std::test_rng;
    use rand_core::RngCore;

    use crate::{bn254_fr::FrInteral, maybe_u64::MaybeU64Coversion};

    use super::MaybeU64;

    type TestField = MaybeU64<FrInteral>;

    #[test]
    fn test_conversion() {
        let mut rng = test_rng();

        for _ in 0..100 {
            let a64 = rng.next_u64();
            let a = TestField::from(a64);
            let b = a.to_full();
            let c = b.to_u64();
            assert_eq!(a, c)
        }
    }

    #[test]
    fn addition() {
        let mut rng = test_rng();

        for _ in 0..100 {
            let a = TestField::random_u64(&mut rng);
            let b = TestField::random_u64(&mut rng);
            let c = TestField::U64(u64::MAX);

            let t1 = (a + b) + c;
            let t2 = a + (b + c);
            let t3 = (a + c) + b;

            assert_eq!(t1, t2);
            assert_eq!(t1, t3);
        }
    }
}
