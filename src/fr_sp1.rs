use crate::{
    impl_add_binop_specify_output,
    impl_binops_additive_specify_output,
    impl_binops_multiplicative_mixed, impl_sub_binop_specify_output, impl_sum_prod,
};
use core::arch::asm;
use core::ops::{Add, Mul, Neg, Sub};
use ff::ExtraArithmetic;
use ff::PrimeField;
use ff::{FromUniformBytes, MulAddAssign};
use rand::RngCore;
use std::convert::TryInto;
use std::io;
use std::io::{Read, Write};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

/// redirected to syscall_bn254_scalar_arith.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(align(32))]
pub struct Fr(pub(crate) [u32; 8]);

#[inline]
fn syscall_bn254_scalar_mul(p: *mut u32, q: *const u32) {
    const BN254_SCALAR_MUL: u32 = 0x00_01_01_80;
    unsafe {
        asm!(
        "ecall",
        in("t0") BN254_SCALAR_MUL,
        in("a0") p,
        in("a1") q,
        );
    }
}
#[inline]
fn syscall_bn254_scalar_mac(ret: *mut u32, a: *const u32, b: *const u32) {
    const BN254_SCALAR_MAC: u32 = 0x00_01_01_81;
    unsafe {
        asm!(
        "ecall",
        in("t0") BN254_SCALAR_MAC,
        in("a0") ret,
        in("a1") &[a, b],
        );
    }
}

const MODULUS: Fr = Fr([
    0xf0000001, 0x43e1f593, 0x79b97091, 0x2833e848, 0x8181585d, 0xb85045b6, 0xe131a029, 0x30644e72,
]);

const MODULUS_STR: &str = "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001";

/// `GENERATOR = 7 mod r` is a generator of the `r - 1` order multiplicative
/// subgroup, or in other words a primitive root of the field.
const GENERATOR: Fr = Fr([0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);

const S: u32 = 28;

/// GENERATOR^t where t * 2^s + 1 = r
/// with t odd. In other words, this
/// is a 2^s root of unity.
/// `0x3ddb9f5166d18b798865ea93dd31f743215cf6dd39329c8d34f1ed960c37c9c`
const ROOT_OF_UNITY: Fr = Fr([
    0xd34f1ed9, 0x60c37c9c, 0x3215cf6d, 0xd39329c8, 0x98865ea9, 0x3dd31f74, 0x03ddb9f5, 0x166d18b7,
]);

/// 1 / 2 mod r
const TWO_INV: Fr = Fr([
    0xa1f0fac9, 0xf8000001, 0x9419f424, 0x3cdcb848, 0xdc2822db, 0x40c0ac2e, 0x18322739, 0x7098d014,
]);

/// 1 / ROOT_OF_UNITY mod r
const ROOT_OF_UNITY_INV: Fr = Fr([
    0x0ed3e50a, 0x414e6dba, 0xb22625f5, 0x9115aba7, 0x1bbe5871, 0x80f34361, 0x04812717, 0x4daabc26,
]);

/// GENERATOR^{2^s} where t * 2^s + 1 = r with t odd. In other words, this is a t root of unity.
/// 0x09226b6e22c6f0ca64ec26aad4c86e715b5f898e5e963f25870e56bbe533e9a2
const DELTA: Fr = Fr([
    0x870e56bb, 0xe533e9a2, 0x5b5f898e, 0x5e963f25, 0x64ec26aa, 0xd4c86e71, 0x09226b6e, 0x22c6f0ca,
]);

/// `ZETA^3 = 1 mod r` where `ZETA^2 != 1 mod r`
const ZETA: Fr = Fr([
    0x8b17ea66, 0xb99c90dd, 0x5bfc4108, 0x8d8daaa7, 0xb3c4d79d, 0x41a91758, 0x00, 0x00,
]);

/// Compute a - (b + borrow), returning the result and the new borrow.
#[inline(always)]
pub(crate) const fn sbb_u32(a: u32, b: u32, borrow: u32) -> (u32, u32) {
    let ret = (a as u64).wrapping_sub((b as u64) + ((borrow >> 31) as u64));
    (ret as u32, (ret >> 32) as u32)
}

static ONE: Fr = Fr::one();

impl Fr {
    #[inline]
    pub const fn zero() -> Self {
        Fr([0, 0, 0, 0, 0, 0, 0, 0])
    }

    #[inline]
    pub const fn one() -> Self {
        Fr([1, 0, 0, 0, 0, 0, 0, 0])
    }

    pub fn from_bytes(bytes: &[u8; 32]) -> CtOption<Fr> {
        let mut tmp = [0, 0, 0, 0, 0, 0, 0, 0];

        tmp[0] = u32::from_le_bytes(bytes[0..4].try_into().unwrap());
        tmp[1] = u32::from_le_bytes(bytes[4..8].try_into().unwrap());
        tmp[2] = u32::from_le_bytes(bytes[8..12].try_into().unwrap());
        tmp[3] = u32::from_le_bytes(bytes[12..16].try_into().unwrap());
        tmp[4] = u32::from_le_bytes(bytes[16..20].try_into().unwrap());
        tmp[5] = u32::from_le_bytes(bytes[20..24].try_into().unwrap());
        tmp[6] = u32::from_le_bytes(bytes[24..28].try_into().unwrap());
        tmp[7] = u32::from_le_bytes(bytes[28..32].try_into().unwrap());

        let (_, borrow) = sbb_u32(tmp[0], MODULUS.0[0], 0);
        let (_, borrow) = sbb_u32(tmp[1], MODULUS.0[1], borrow);
        let (_, borrow) = sbb_u32(tmp[2], MODULUS.0[2], borrow);
        let (_, borrow) = sbb_u32(tmp[3], MODULUS.0[3], borrow);
        let (_, borrow) = sbb_u32(tmp[4], MODULUS.0[4], borrow);
        let (_, borrow) = sbb_u32(tmp[5], MODULUS.0[5], borrow);
        let (_, borrow) = sbb_u32(tmp[6], MODULUS.0[6], borrow);
        let (_, borrow) = sbb_u32(tmp[7], MODULUS.0[7], borrow);

        let is_some = (borrow as u8) & 1;

        CtOption::new(Fr(tmp), Choice::from(is_some))
    }

    pub const fn from_raw(limbs: [u64; 4]) -> Fr {
        // FIXME: handle limbs that are larger than modulus.
        let mut tmp = [0, 0, 0, 0, 0, 0, 0, 0];

        tmp[0] = (limbs[0] & 0xffffffff) as u32;
        tmp[1] = ((limbs[0] >> 32) & 0xffffffff) as u32;
        tmp[2] = (limbs[1] & 0xffffffff) as u32;
        tmp[3] = ((limbs[1] >> 32) & 0xffffffff) as u32;
        tmp[4] = (limbs[2] & 0xffffffff) as u32;
        tmp[5] = ((limbs[2] >> 32) & 0xffffffff) as u32;
        tmp[6] = (limbs[3] & 0xffffffff) as u32;
        tmp[7] = ((limbs[3] >> 32) & 0xffffffff) as u32;

        Fr(tmp)
    }

    pub const fn size() -> usize {
        32
    }

    pub fn mul(&self, rhs: &Self) -> Fr {
        let mut p = core::mem::MaybeUninit::<[u32; 8]>::uninit();

        let src_ptr = self.0.as_ptr() as *const u32;
        let p_ptr = p.as_mut_ptr() as *mut u32;
        let q_ptr = rhs.0.as_ptr() as *const u32;

        unsafe {
            core::ptr::copy(src_ptr, p_ptr, 8);
            syscall_bn254_scalar_mul(p_ptr, q_ptr);
        }

        let p = unsafe { p.assume_init() };
        Fr(p)
    }

    pub fn sub(&self, _rhs: &Self) -> Fr {
        todo!()
    }

    pub fn add(&self, rhs: &Self) -> Fr {
        println!("cycle-tracker-start: Fr::add");
        let mut p = core::mem::MaybeUninit::<[u32; 8]>::uninit();

        let src_ptr = self.0.as_ptr() as *const u32;
        let p_ptr = p.as_mut_ptr() as *mut u32;
        let q_ptr = rhs.0.as_ptr() as *const u32;

        unsafe {
            core::ptr::copy(src_ptr, p_ptr, 8);
            syscall_bn254_scalar_mac(p_ptr, q_ptr, ONE.0.as_ptr() as *const u32);
        }

        let p = unsafe { p.assume_init() };
        println!("cycle-tracker-end: Fr::add");
        Fr(p)
    }
}

impl_binops_additive_specify_output!(Fr, Fr, Fr);
impl_binops_multiplicative_mixed!(Fr, Fr, Fr);
impl_sum_prod!(Fr);

impl ::core::ops::SubAssign<Fr> for Fr {
    #[inline]
    fn sub_assign(&mut self, rhs: Fr) {
        self.sub_assign(&rhs);
    }
}

impl<'b> ::core::ops::SubAssign<&'b Fr> for Fr {
    #[inline]
    fn sub_assign(&mut self, rhs: &'b Fr) {
        *self = &*self - rhs;
    }
}

impl ::core::ops::AddAssign<Fr> for Fr {
    #[inline]
    fn add_assign(&mut self, rhs: Fr) {
        self.add_assign(&rhs);
    }
}

impl<'b> ::core::ops::AddAssign<&'b Fr> for Fr {
    #[inline]
    fn add_assign(&mut self, rhs: &'b Fr) {
        syscall_bn254_scalar_mac(
            self as *mut _ as *mut u32,
            rhs as *const _ as *const u32,
            &ONE as *const _ as *const u32,
        );
    }
}

impl core::ops::MulAssign<Fr> for Fr {
    #[inline]
    fn mul_assign(&mut self, rhs: Fr) {
        self.mul_assign(&rhs);
    }
}

impl<'b> core::ops::MulAssign<&'b Fr> for Fr {
    #[inline]
    fn mul_assign(&mut self, rhs: &'b Fr) {
        syscall_bn254_scalar_mul(self as *mut _ as *mut u32, rhs as *const _ as *const u32);
    }
}

impl ExtraArithmetic for Fr {}

impl MulAddAssign for Fr {
    #[inline]
    fn mul_add_assign(&mut self, a: Self, b: Self) {
        self.mul_add_assign(&a, &b);
    }
}

impl<'a> MulAddAssign<Fr, &'a Fr> for Fr {
    #[inline]
    fn mul_add_assign(&mut self, a: Self, b: &'a Self) {
        self.mul_add_assign(&a, b);
    }
}

impl<'a> MulAddAssign<&'a Fr, Fr> for Fr {
    #[inline]
    fn mul_add_assign(&mut self, a: &'a Self, b: Self) {
        self.mul_add_assign(a, &b);
    }
}

impl<'a, 'b> MulAddAssign<&'a Fr, &'b Fr> for Fr {
    #[inline]
    fn mul_add_assign(&mut self, a: &'a Self, b: &'b Self) {
        syscall_bn254_scalar_mac(
            self as *mut _ as *mut u32,
            a as *const _ as *const u32,
            b as *const _ as *const u32,
        );
    }
}

impl ff::Field for Fr {
    const ZERO: Self = Self::zero();
    const ONE: Self = Self::one();

    fn double(&self) -> Fr {
        self + self
    }

    #[inline]
    fn square(&self) -> Fr {
        self * self
    }

    fn invert(&self) -> CtOption<Fr> {
        todo!()
    }

    fn random(_rng: impl RngCore) -> Fr {
        todo!()
    }

    fn sqrt_ratio(_num: &Self, _div: &Self) -> (Choice, Self) {
        todo!()
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
        Self::from_bytes(&repr)
    }

    fn to_repr(&self) -> Self::Repr {
        let mut r = [0u8; 32];

        r[0..4].copy_from_slice(&self.0[0].to_le_bytes());
        r[4..8].copy_from_slice(&self.0[1].to_le_bytes());
        r[8..12].copy_from_slice(&self.0[2].to_le_bytes());
        r[12..16].copy_from_slice(&self.0[3].to_le_bytes());
        r[16..20].copy_from_slice(&self.0[4].to_le_bytes());
        r[20..24].copy_from_slice(&self.0[5].to_le_bytes());
        r[24..28].copy_from_slice(&self.0[6].to_le_bytes());
        r[28..32].copy_from_slice(&self.0[7].to_le_bytes());

        r
    }

    fn from_u128(v: u128) -> Self {
        let a0 = v as u32;
        let a1 = (v >> 32) as u32;
        let a2 = (v >> 64) as u32;
        let a3 = (v >> 96) as u32;
        let mut buf = [0u8; 32];

        buf[0..4].copy_from_slice(&a0.to_le_bytes());
        buf[4..8].copy_from_slice(&a1.to_le_bytes());
        buf[8..12].copy_from_slice(&a2.to_le_bytes());
        buf[12..16].copy_from_slice(&a3.to_le_bytes());
        Self::from_repr_vartime(buf).unwrap()
    }

    fn is_odd(&self) -> Choice {
        Choice::from((self.0[0] as u8) & 0x01_u8)
    }
}

impl crate::serde::SerdeObject for Fr {
    fn from_raw_bytes_unchecked(_bytes: &[u8]) -> Self {
        todo!()
    }

    fn from_raw_bytes(_bytes: &[u8]) -> Option<Self> {
        todo!()
    }

    fn to_raw_bytes(&self) -> Vec<u8> {
        todo!()
    }

    fn read_raw_unchecked<R: Read>(_reader: &mut R) -> Self {
        todo!()
    }

    fn read_raw<R: Read>(_reader: &mut R) -> io::Result<Self> {
        todo!()
    }

    fn write_raw<W: Write>(&self, _writer: &mut W) -> io::Result<()> {
        todo!()
    }
}

impl From<u64> for Fr {
    fn from(val: u64) -> Fr {
        let v_lo = val as u32;
        let v_hi = (val >> 32) as u32;
        Fr([v_lo, v_hi, 0, 0, 0, 0, 0, 0])
    }
}

impl FromUniformBytes<64> for Fr {
    fn from_uniform_bytes(_bytes: &[u8; 64]) -> Self {
        todo!()
    }
}

impl ConstantTimeEq for Fr {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0[0].ct_eq(&other.0[0])
            & self.0[1].ct_eq(&other.0[1])
            & self.0[2].ct_eq(&other.0[2])
            & self.0[3].ct_eq(&other.0[3])
    }
}

impl core::cmp::Ord for Fr {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        let left = self.to_repr();
        let right = other.to_repr();
        left.iter()
            .zip(right.iter())
            .rev()
            .find_map(|(left_byte, right_byte)| match left_byte.cmp(right_byte) {
                core::cmp::Ordering::Equal => None,
                res => Some(res),
            })
            .unwrap_or(core::cmp::Ordering::Equal)
    }
}

impl core::cmp::PartialOrd for Fr {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl ConditionallySelectable for Fr {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fr([
            u32::conditional_select(&a.0[0], &b.0[0], choice),
            u32::conditional_select(&a.0[1], &b.0[1], choice),
            u32::conditional_select(&a.0[2], &b.0[2], choice),
            u32::conditional_select(&a.0[3], &b.0[3], choice),
            u32::conditional_select(&a.0[4], &b.0[4], choice),
            u32::conditional_select(&a.0[5], &b.0[5], choice),
            u32::conditional_select(&a.0[6], &b.0[6], choice),
            u32::conditional_select(&a.0[7], &b.0[7], choice),
        ])
    }
}

impl ff::WithSmallOrderMulGroup<3> for Fr {
    const ZETA: Self = ZETA;
}

impl Default for Fr {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<'a> Neg for &'a Fr {
    type Output = Fr;

    #[inline]
    fn neg(self) -> Fr {
        unimplemented!()
    }
}

impl Neg for Fr {
    type Output = Fr;

    #[inline]
    fn neg(self) -> Fr {
        unimplemented!()
    }
}

impl<'a, 'b> Add<&'b Fr> for &'a Fr {
    type Output = Fr;

    #[inline]
    fn add(self, rhs: &'b Fr) -> Fr {
        self.add(rhs)
    }
}

impl<'a, 'b> Sub<&'b Fr> for &'a Fr {
    type Output = Fr;

    #[inline]
    fn sub(self, rhs: &'b Fr) -> Fr {
        self.sub(rhs)
    }
}

impl<'a, 'b> Mul<&'b Fr> for &'a Fr {
    type Output = Fr;

    #[inline]
    fn mul(self, rhs: &'b Fr) -> Fr {
        self.mul(rhs)
    }
}
