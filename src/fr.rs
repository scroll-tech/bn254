#[cfg(feature = "asm")]
use crate::bn256::assembly::field_arithmetic_asm;
#[cfg(not(feature = "asm"))]
use crate::{field_arithmetic, field_specific};

use crate::arithmetic::{adc, mac, sbb};
use crate::{
    field_bits, field_common, impl_add_binop_specify_output, impl_binops_additive,
    impl_binops_additive_specify_output, impl_binops_multiplicative,
    impl_binops_multiplicative_mixed, impl_sub_binop_specify_output, impl_sum_prod,
};
use core::convert::TryInto;
use core::fmt;
use core::ops::{Add, Mul, Neg, Sub};
use ff::{ExtraArithmetic, MulAddAssign};
use ff::{FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
use rand::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[cfg(feature = "derive_serde")]
use serde::{Deserialize, Serialize};

/// This represents an element of $\mathbb{F}_r$ where
///
/// `r = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001`
///
/// is the scalar field of the BN254 curve.
// The internal representation of this type is four 64-bit unsigned
// integers in little-endian order. `Fr` values are always in
// Montgomery form; i.e., Fr(a) = aR mod r, with R = 2^256.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "derive_serde", derive(Serialize, Deserialize))]
pub struct Fr(pub(crate) [u64; 4]);

/// Constant representing the modulus
/// r = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
const MODULUS: Fr = Fr([
    0x43e1f593f0000001,
    0x2833e84879b97091,
    0xb85045b68181585d,
    0x30644e72e131a029,
]);

/// The modulus as u32 limbs.
#[cfg(not(target_pointer_width = "64"))]
const MODULUS_LIMBS_32: [u32; 8] = [
    0xf000_0001,
    0x43e1_f593,
    0x79b9_7091,
    0x2833_e848,
    0x8181_585d,
    0xb850_45b6,
    0xe131_a029,
    0x3064_4e72,
];

const MODULUS_STR: &str = "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001";

/// INV = -(r^{-1} mod 2^64) mod 2^64
const INV: u64 = 0xc2e1f593efffffff;

/// `R = 2^256 mod r`
/// `0xe0a77c19a07df2f666ea36f7879462e36fc76959f60cd29ac96341c4ffffffb`
const R: Fr = Fr([
    0xac96341c4ffffffb,
    0x36fc76959f60cd29,
    0x666ea36f7879462e,
    0x0e0a77c19a07df2f,
]);

/// `R^2 = 2^512 mod r`
/// `0x216d0b17f4e44a58c49833d53bb808553fe3ab1e35c59e31bb8e645ae216da7`
const R2: Fr = Fr([
    0x1bb8e645ae216da7,
    0x53fe3ab1e35c59e3,
    0x8c49833d53bb8085,
    0x0216d0b17f4e44a5,
]);

/// `R^3 = 2^768 mod r`
/// `0xcf8594b7fcc657c893cc664a19fcfed2a489cbe1cfbb6b85e94d8e1b4bf0040`
const R3: Fr = Fr([
    0x5e94d8e1b4bf0040,
    0x2a489cbe1cfbb6b8,
    0x893cc664a19fcfed,
    0x0cf8594b7fcc657c,
]);

/// `GENERATOR = 7 mod r` is a generator of the `r - 1` order multiplicative
/// subgroup, or in other words a primitive root of the field.
const GENERATOR: Fr = Fr::from_raw([0x07, 0x00, 0x00, 0x00]);

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

/// GENERATOR^{2^s} where t * 2^s + 1 = r with t odd. In other words, this is a t root of unity.
/// 0x09226b6e22c6f0ca64ec26aad4c86e715b5f898e5e963f25870e56bbe533e9a2
const DELTA: Fr = Fr::from_raw([
    0x870e56bbe533e9a2,
    0x5b5f898e5e963f25,
    0x64ec26aad4c86e71,
    0x09226b6e22c6f0ca,
]);

/// `ZETA^3 = 1 mod r` where `ZETA^2 != 1 mod r`
const ZETA: Fr = Fr::from_raw([
    0x8b17ea66b99c90dd,
    0x5bfc41088d8daaa7,
    0xb3c4d79d41a91758,
    0x00,
]);

impl_binops_additive!(Fr, Fr);
impl_binops_multiplicative!(Fr, Fr);
field_common!(
    Fr,
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
impl_sum_prod!(Fr);

#[cfg(not(feature = "asm"))]
field_arithmetic!(Fr, MODULUS, INV, sparse);
#[cfg(feature = "asm")]
field_arithmetic_asm!(Fr, MODULUS, INV);

#[cfg(target_pointer_width = "64")]
field_bits!(Fr, MODULUS);
#[cfg(not(target_pointer_width = "64"))]
field_bits!(Fr, MODULUS, MODULUS_LIMBS_32);

impl Fr {
    pub const fn size() -> usize {
        32
    }
}

impl ff::Field for Fr {
    const ZERO: Self = Self::zero();
    const ONE: Self = Self::one();

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

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    fn invert(&self) -> CtOption<Self> {
        let tmp = self.pow([
            0x43e1f593efffffff,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ]);

        CtOption::new(tmp, !self.ct_eq(&Self::zero()))
    }

    fn sqrt(&self) -> CtOption<Self> {
        /// `(t - 1) // 2` where t * 2^s + 1 = p with t odd.
        const T_MINUS1_OVER2: [u64; 4] = [
            0xcdcb848a1f0fac9f,
            0x0c0ac2e9419f4243,
            0x098d014dc2822db4,
            0x0000000183227397,
        ];
        ff::helpers::sqrt_tonelli_shanks(self, T_MINUS1_OVER2)
    }

    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        ff::helpers::sqrt_ratio_generic(num, div)
    }
}

impl ff::PrimeField for Fr {
    type Repr = [u8; 32];

    const NUM_BITS: u32 = 254;
    const CAPACITY: u32 = 253;
    const MODULUS: &'static str = MODULUS_STR;
    const MULTIPLICATIVE_GENERATOR: Self = GENERATOR;
    const ROOT_OF_UNITY: Self = ROOT_OF_UNITY;
    const ROOT_OF_UNITY_INV: Self = ROOT_OF_UNITY_INV;
    const TWO_INV: Self = TWO_INV;
    const DELTA: Self = DELTA;
    const S: u32 = S;

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let mut tmp = Fr([0, 0, 0, 0]);

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
        let tmp = Fr::montgomery_reduce(&[self.0[0], self.0[1], self.0[2], self.0[3], 0, 0, 0, 0]);

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
}

impl FromUniformBytes<64> for Fr {
    /// Converts a 512-bit little endian integer into
    /// an `Fr` by reducing by the modulus.
    fn from_uniform_bytes(bytes: &[u8; 64]) -> Self {
        Self::from_u512([
            u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
            u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
            u64::from_le_bytes(bytes[32..40].try_into().unwrap()),
            u64::from_le_bytes(bytes[40..48].try_into().unwrap()),
            u64::from_le_bytes(bytes[48..56].try_into().unwrap()),
            u64::from_le_bytes(bytes[56..64].try_into().unwrap()),
        ])
    }
}

impl WithSmallOrderMulGroup<3> for Fr {
    const ZETA: Self = ZETA;
}

impl ExtraArithmetic for Fr {}

impl MulAddAssign for Fr {
    fn mul_add_assign(&mut self, a: Self, b: Self) {
        self.mul_add_assign(&a, &b)
    }
}

impl<'a> MulAddAssign<Fr, &'a Fr> for Fr {
    fn mul_add_assign(&mut self, a: Self, b: &'a Self) {
        self.mul_add_assign(&a, b)
    }
}

impl<'a> MulAddAssign<&'a Fr, Fr> for Fr {
    fn mul_add_assign(&mut self, a: &'a Self, b: Self) {
        self.mul_add_assign(a, &b)
    }
}

impl<'a, 'b> MulAddAssign<&'a Fr, &'b Fr> for Fr {
    fn mul_add_assign(&mut self, a: &'a Self, b: &'b Self) {
        *self = *self + *a + *b;
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
        let v = (Fr::TWO_INV).square().sqrt().unwrap();
        assert!(v == Fr::TWO_INV || (-v) == Fr::TWO_INV);

        for _ in 0..10000 {
            let a = Fr::random(OsRng);
            let mut b = a;
            b = b.square();

            let b = b.sqrt().unwrap();
            let mut negb = b;
            negb = negb.neg();

            assert!(a == b || a == negb);
        }
    }

    #[test]
    fn test_field() {
        crate::tests::field::random_field_tests::<Fr>("bn256 scalar".to_string());
    }

    #[test]
    fn test_delta() {
        assert_eq!(Fr::DELTA, GENERATOR.pow([1u64 << Fr::S]));
        assert_eq!(Fr::DELTA, Fr::MULTIPLICATIVE_GENERATOR.pow([1u64 << Fr::S]));
    }

    #[test]
    fn test_from_u512() {
        assert_eq!(
            Fr::from_raw([
                0x7e7140b5196b9e6f,
                0x9abac9e4157b6172,
                0xf04bc41062fd7322,
                0x1185fa9c9fef6326,
            ]),
            Fr::from_u512([
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
    #[cfg(feature = "bits")]
    fn test_bits() {
        crate::tests::field::random_bits_tests::<Fr>("fr".to_string());
    }

    #[test]
    fn test_serialization() {
        crate::tests::field::random_serialization_test::<Fr>("fr".to_string());
        #[cfg(feature = "derive_serde")]
        crate::tests::field::random_serde_test::<Fr>("fr".to_string());
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
        let _message = "serialization fr";
        let start = start_timer!(|| _message);
        // failure check
        for _ in 0..1000000 {
            let rand_word = [(); 4].map(|_| rng.next_u64());
            let a = Fr(rand_word);
            let rand_bytes = a.to_raw_bytes();
            match is_less_than(&rand_word, &MODULUS.0) {
                false => {
                    assert!(Fr::from_raw_bytes(&rand_bytes).is_none());
                }
                _ => {
                    assert_eq!(Fr::from_raw_bytes(&rand_bytes), Some(a));
                }
            }
        }
        end_timer!(start);
    }
}
