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

#[cfg(test)]
mod test {
    use std::ops::{AddAssign, SubAssign};

    use ark_std::test_rng;

    use crate::{bn254_fr::FrInteral, maybe_u64::MaybeU64Coversion, MaybeU64};

    type MockField = MaybeU64<FrInteral>;

    #[test]
    fn subtraction() {
        let mut rng = test_rng();

        for _ in 0..100 {
            let a = MockField::random_u64(&mut rng);
            let b = MockField::U64(u64::MAX);

            let mut t0 = a; // (a - b)
            t0.sub_assign(&b);

            let mut t1 = b; // (b - a)
            t1.sub_assign(&a);

            let mut t2 = t0; // (a - b) + (b - a) = 0
            t2.add_assign(&t1);

            assert_eq!(t2.to_u64(), MockField::from(0));
        }
    }
}
