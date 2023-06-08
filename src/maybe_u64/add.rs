use std::iter::Sum;
use std::ops::{Add, AddAssign};

use ff::{Field, PrimeField};

use crate::arithmetic::adc;
use crate::MaybeU64;

impl<'a, 'b, F> Add<&'b MaybeU64<F>> for &'a MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    type Output = MaybeU64<F>;

    fn add(self, rhs: &'b MaybeU64<F>) -> Self::Output {
        match (self, rhs) {
            (MaybeU64::U64(a), MaybeU64::U64(b)) => {
                let (c, carry) = adc(*a, *b, 0);
                match carry {
                    0 => MaybeU64::U64(c),
                    1 => MaybeU64::Full(
                        F::from_repr(
                            [
                                c.to_le_bytes().as_ref(),
                                &[carry as u8],
                                vec![0; 23].as_ref(),
                            ]
                            .concat()
                            .try_into()
                            .unwrap(),
                        )
                        .unwrap(),
                    ),
                    _ => panic!("invalid carry: {}", carry),
                }
            }
            (MaybeU64::U64(a), MaybeU64::Full(b)) => MaybeU64::Full(F::from(*a) + b),
            (MaybeU64::Full(a), MaybeU64::U64(b)) => MaybeU64::Full(*a + F::from(*b)),
            (MaybeU64::Full(a), MaybeU64::Full(b)) => MaybeU64::Full(*a + *b),
        }
    }
}

impl<'a, F> Add<MaybeU64<F>> for &'a MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    type Output = MaybeU64<F>;

    fn add(self, rhs: MaybeU64<F>) -> Self::Output {
        self + &rhs
    }
}

impl<'b, F> Add<&'b MaybeU64<F>> for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    type Output = MaybeU64<F>;

    fn add(self, rhs: &'b MaybeU64<F>) -> Self::Output {
        &self + rhs
    }
}

impl<F> Add<MaybeU64<F>> for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    type Output = MaybeU64<F>;

    fn add(self, rhs: MaybeU64<F>) -> Self::Output {
        &self + &rhs
    }
}

impl<F> AddAssign<MaybeU64<F>> for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    #[inline]
    fn add_assign(&mut self, rhs: MaybeU64<F>) {
        *self = &*self + &rhs;
    }
}

impl<'b, F> AddAssign<&'b MaybeU64<F>> for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    #[inline]
    fn add_assign(&mut self, rhs: &'b MaybeU64<F>) {
        *self = &*self + rhs;
    }
}

impl<F, T> Sum<T> for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
    T: core::borrow::Borrow<Self>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Self::zero(), |acc, item| acc + item.borrow())
    }
}
