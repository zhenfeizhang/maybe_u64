use std::ops::{Sub, SubAssign};

use ff::PrimeField;

use crate::{arithmetic::sbb, MaybeU64};

impl<'a, 'b, F> Sub<&'b MaybeU64<F>> for &'a MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    type Output = MaybeU64<F>;

    fn sub(self, rhs: &'b MaybeU64<F>) -> Self::Output {
        match (self, rhs) {
            (MaybeU64::U64(a), MaybeU64::U64(b)) => {
                let (c, carry) = sbb(*a, *b, 0);
                match carry {
                    0 => MaybeU64::U64(c),
                    u64::MAX => MaybeU64::Full(F::from(*a) - F::from(*b)),
                    _ => panic!("invalid carry: {}", carry),
                }
            }
            (MaybeU64::U64(a), MaybeU64::Full(b)) => MaybeU64::Full(F::from(*a) - b),
            (MaybeU64::Full(a), MaybeU64::U64(b)) => MaybeU64::Full(*a - F::from(*b)),
            (MaybeU64::Full(a), MaybeU64::Full(b)) => MaybeU64::Full(*a - *b),
        }
    }
}

impl<'a, F> Sub<MaybeU64<F>> for &'a MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    type Output = MaybeU64<F>;

    fn sub(self, rhs: MaybeU64<F>) -> Self::Output {
        self - &rhs
    }
}

impl<'b, F> Sub<&'b MaybeU64<F>> for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    type Output = MaybeU64<F>;

    fn sub(self, rhs: &'b MaybeU64<F>) -> Self::Output {
        &self - rhs
    }
}

impl<F> Sub<MaybeU64<F>> for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    type Output = MaybeU64<F>;

    fn sub(self, rhs: MaybeU64<F>) -> Self::Output {
        &self - &rhs
    }
}

impl<F> SubAssign<MaybeU64<F>> for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    #[inline]
    fn sub_assign(&mut self, rhs: MaybeU64<F>) {
        *self = &*self - &rhs;
    }
}

impl<'b, F> SubAssign<&'b MaybeU64<F>> for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    #[inline]
    fn sub_assign(&mut self, rhs: &'b MaybeU64<F>) {
        *self = &*self - rhs;
    }
}
