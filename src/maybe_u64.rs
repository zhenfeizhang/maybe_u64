use ff::{Field, PrimeField};
use rand_core::RngCore;
use serde::{Deserialize, Serialize};
use subtle::{Choice, CtOption};

mod add;
mod misc;
mod mul;
mod neg;
mod sub;

#[derive(Clone, Copy, Debug, Eq, Hash, Serialize, Deserialize)]
/// Struct for a 256-bits field elements.
/// - U64: if the element is less than 1<<64
/// - Full: otherwise
///
/// This allows for faster computation with u64 ops.
pub enum MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
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

impl<F> From<u64> for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    fn from(value: u64) -> Self {
        Self::U64(value)
    }
}

impl<F> Field for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    fn random(rng: impl RngCore) -> Self {
        Self::Full(F::random(rng))
    }

    fn zero() -> Self {
        Self::U64(0)
    }

    fn one() -> Self {
        Self::U64(1)
    }

    fn square(&self) -> Self {
        self * self
    }

    fn double(&self) -> Self {
        self + self
    }

    fn invert(&self) -> CtOption<Self> {
        match *self {
            MaybeU64::U64(a) => F::from(a).invert().map(|x| MaybeU64::Full(x)),
            MaybeU64::Full(a) => a.invert().map(|x| MaybeU64::Full(x)),
        }
    }

    fn sqrt(&self) -> CtOption<Self> {
        match *self {
            MaybeU64::U64(a) => F::from(a).sqrt().map(|x| MaybeU64::Full(x)),
            MaybeU64::Full(a) => a.sqrt().map(|x| MaybeU64::Full(x)),
        }
    }
}

impl<F> PrimeField for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    const CAPACITY: u32 = F::CAPACITY;
    const NUM_BITS: u32 = F::NUM_BITS;
    const S: u32 = F::S;

    type Repr = F::Repr;

    fn from_str_vartime(s: &str) -> Option<Self> {
        F::from_str_vartime(s).map(|x| Self::Full(x))
    }

    fn from_repr(repr: [u8; 32]) -> CtOption<Self> {
        let is_u64 = repr.iter().skip(8).all(|x| *x == 0);
        if is_u64 {
            CtOption::new(
                Self::U64(u64::from_le_bytes(repr[..0].try_into().unwrap())),
                1.into(),
            )
        } else {
            F::from_repr(repr).map(|x| Self::Full(x))
        }
    }

    fn to_repr(&self) -> [u8; 32] {
        match *self {
            MaybeU64::Full(f) => f.to_repr(),
            MaybeU64::U64(f) => [f.to_le_bytes().as_ref(), vec![0u8; 24].as_ref()]
                .concat()
                .try_into()
                .unwrap(),
        }
    }

    fn is_odd(&self) -> Choice {
        match *self {
            MaybeU64::Full(f) => f.is_odd(),
            MaybeU64::U64(f) => ((f % 2 == 1) as u8).into(),
        }
    }

    fn multiplicative_generator() -> Self {
        // Requires the multiplicative generator is 64 bits
        // which is true for BN254's scalar field
        Self::Full(F::multiplicative_generator()).to_u64()
    }

    fn root_of_unity() -> Self {
        Self::Full(F::root_of_unity())
    }
}

#[cfg(test)]
mod test {
    use ark_std::test_rng;
    use ff::{PrimeField, Field};
    use rand_core::RngCore;

    use crate::{bn254_fr::FrInteral, maybe_u64::MaybeU64Coversion};

    use super::MaybeU64;

    type MockField = MaybeU64<FrInteral>;

    #[test]
    fn test_conversion() {
        let mut rng = test_rng();

        for _ in 0..100 {
            let a64 = rng.next_u64();
            let a = MockField::from(a64);
            let b = a.to_full();
            let c = b.to_u64();
            assert_eq!(a, c)
        }
    }

    #[test]
    fn test_field() {
        crate::tests::field::random_field_tests::<MockField>("test field".to_string());
    }

    #[test]
    fn test_root_of_unity() {
        assert_eq!(
            MockField::root_of_unity().pow_vartime(&[1 << MockField::S, 0, 0, 0]),
            MockField::one()
        );
    }
}
