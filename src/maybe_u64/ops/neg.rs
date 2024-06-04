use std::ops::Neg;

use ff::PrimeField;

use crate::MaybeU64;

impl<F> Neg for MaybeU64<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    type Output = MaybeU64<F>;

    fn neg(self) -> <Self as Neg>::Output {
        match self {
            MaybeU64::U64(a) => MaybeU64::Full(-F::from(a)),
            MaybeU64::Full(a) => MaybeU64::Full(-a),
        }
    }
}
