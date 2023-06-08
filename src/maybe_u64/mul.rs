use std::ops::{Mul, MulAssign};

use ff::PrimeField;

use crate::{arithmetic::mac, MaybeU64};

impl<'a, 'b, F> Mul<&'b MaybeU64<F>> for &'a MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    type Output = MaybeU64<F>;

    fn mul(self, rhs: &'b MaybeU64<F>) -> Self::Output {
        match (self, rhs) {
            (MaybeU64::U64(a), MaybeU64::U64(b)) => {
                let (c, carry) = mac(0, *a, *b, 0);
                match carry {
                    0 => MaybeU64::U64(c),
                    _ => MaybeU64::Full(
                        F::from_repr(
                            [
                                c.to_le_bytes().as_ref(),
                                carry.to_le_bytes().as_ref(),
                                vec![0u8; 16].as_ref(),
                            ]
                            .concat()
                            .try_into()
                            .unwrap(),
                        )
                        .unwrap(),
                    ),
                }
            }
            (MaybeU64::U64(a), MaybeU64::Full(b)) => MaybeU64::Full(F::from(*a) * b),
            (MaybeU64::Full(a), MaybeU64::U64(b)) => MaybeU64::Full(*a * F::from(*b)),
            (MaybeU64::Full(a), MaybeU64::Full(b)) => MaybeU64::Full(*a * *b),
        }
    }
}

impl<'a, F> Mul<MaybeU64<F>> for &'a MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    type Output = MaybeU64<F>;

    fn mul(self, rhs: MaybeU64<F>) -> Self::Output {
        self * &rhs
    }
}

impl<'b, F> Mul<&'b MaybeU64<F>> for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    type Output = MaybeU64<F>;

    fn mul(self, rhs: &'b MaybeU64<F>) -> Self::Output {
        &self * rhs
    }
}

impl<F> Mul<MaybeU64<F>> for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    type Output = MaybeU64<F>;

    fn mul(self, rhs: MaybeU64<F>) -> Self::Output {
        &self * &rhs
    }
}

impl<F> MulAssign<MaybeU64<F>> for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    #[inline]
    fn mul_assign(&mut self, rhs: MaybeU64<F>) {
        *self = &*self * &rhs;
    }
}

impl<'b, F> MulAssign<&'b MaybeU64<F>> for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    #[inline]
    fn mul_assign(&mut self, rhs: &'b MaybeU64<F>) {
        *self = &*self * rhs;
    }
}

#[cfg(test)]
mod test {
    use std::ops::MulAssign;

    use ark_std::test_rng;

    use crate::{bn254_fr::FrInteral, maybe_u64::MaybeU64Coversion, MaybeU64};

    type MockField = MaybeU64<FrInteral>;

    #[test]
    fn multiplication() {
        let mut rng = test_rng();

        for _ in 0..100 {
            let a = MockField::random_u64(&mut rng);
            let b = MockField::random_field(&mut rng);
            let c = MockField::U64(u64::MAX);

            let mut t0 = a; // (a * b) * c
            t0.mul_assign(&b);
            t0.mul_assign(&c);

            let mut t1 = a; // (a * c) * b
            t1.mul_assign(&c);
            t1.mul_assign(&b);

            let mut t2 = b; // (b * c) * a
            t2.mul_assign(&c);
            t2.mul_assign(&a);

            assert_eq!(t0, t1);
            assert_eq!(t1, t2);
        }
    }
}
