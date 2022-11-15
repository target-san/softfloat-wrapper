use crate::{RoundingMode, SoftFloat, F32, F64};
use softfloat_sys::float16_t;
use std::borrow::Borrow;

/// standard 16-bit float
#[derive(Copy, Clone, Debug)]
pub struct F16(float16_t);

#[cfg(feature = "concordium")]
impl concordium_std::schema::SchemaType for F16 {
    fn get_type() -> concordium_std::schema::Type {
        <<Self as crate::SoftFloat>::Payload as concordium_std::schema::SchemaType>::get_type()
    }
}

#[cfg(feature = "concordium")]
impl concordium_std::Serial for F16 {
    fn serial<W: concordium_std::Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.to_bits().serial(out)
    }
}

#[cfg(feature = "concordium")]
impl concordium_std::Deserial for F16 {
    fn deserial<R: concordium_std::Read>(source: &mut R) -> concordium_std::ParseResult<Self> {
        Ok(Self::from_bits(<Self as crate::SoftFloat>::Payload::deserial(
            source,
        )?))
    }
}

impl Default for F16 {
    fn default() -> Self {
        num_traits::Zero::zero()
    }
}

impl num_traits::Zero for F16 {
    fn zero() -> Self {
        crate::SoftFloat::positive_zero()
    }

    fn is_zero(&self) -> bool {
        crate::SoftFloat::is_zero(self)
    }
}

impl num_traits::One for F16 {
    fn one() -> Self {
        crate::SoftFloat::from_i8(1, crate::DEFAULT_ROUNDING_MODE)
    }
}

impl std::ops::Neg for F16 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        crate::SoftFloat::neg(&self)
    }
}

impl std::ops::Add for F16 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        crate::SoftFloat::add(&self, rhs, crate::DEFAULT_ROUNDING_MODE)
    }
}

impl std::ops::AddAssign for F16 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl std::ops::Sub for F16 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        crate::SoftFloat::sub(&self, rhs, crate::DEFAULT_ROUNDING_MODE)
    }
}

impl std::ops::SubAssign for F16 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl std::ops::Mul for F16 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        crate::SoftFloat::mul(&self, rhs, crate::DEFAULT_ROUNDING_MODE)
    }
}

impl std::ops::MulAssign for F16 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl std::ops::Div for F16 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        crate::SoftFloat::div(&self, rhs, crate::DEFAULT_ROUNDING_MODE)
    }
}

impl std::ops::DivAssign for F16 {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl std::ops::Rem for F16 {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        crate::SoftFloat::rem(&self, rhs, crate::DEFAULT_ROUNDING_MODE)
    }
}

impl std::ops::RemAssign for F16 {
    fn rem_assign(&mut self, rhs: Self) {
        *self = *self % rhs;
    }
}

impl std::cmp::PartialEq for F16 {
    fn eq(&self, other: &Self) -> bool {
        crate::SoftFloat::eq(self, other)
    }
}

impl std::cmp::PartialOrd for F16 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        crate::SoftFloat::compare(self, other)
    }
}

impl SoftFloat for F16 {
    type Payload = u16;

    #[cfg(not(feature = "concordium"))]
    fn from_native_f32(v: f32) -> Self {
        F32::from_bits(v.to_bits()).to_f16(RoundingMode::TiesToEven)
    }

    #[cfg(not(feature = "concordium"))]
    fn from_native_f64(v: f64) -> Self {
        F64::from_bits(v.to_bits()).to_f16(RoundingMode::TiesToEven)
    }

    const MANTISSA_MASK: Self::Payload = 0x3ff;
    const EXPONENT_MASK: Self::Payload = 0x1f;
    const MANTISSA_BITS: usize = 10;
    const EXPONENT_BITS: usize = 5;
    const SIGN_OFFSET: usize = 15;
    const EXPONENT_OFFSET: usize = 10;

    #[inline]
    fn set_payload(&mut self, x: Self::Payload) {
        self.0.v = x;
    }

    #[inline]
    fn from_bits(v: Self::Payload) -> Self {
        Self(float16_t { v })
    }

    #[inline]
    fn to_bits(&self) -> Self::Payload {
        self.0.v
    }

    #[inline]
    fn bits(&self) -> Self::Payload {
        self.to_bits()
    }

    fn add<T: Borrow<Self>>(&self, x: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f16_add(self.0, x.borrow().0) };
        Self(ret)
    }

    fn sub<T: Borrow<Self>>(&self, x: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f16_sub(self.0, x.borrow().0) };
        Self(ret)
    }

    fn mul<T: Borrow<Self>>(&self, x: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f16_mul(self.0, x.borrow().0) };
        Self(ret)
    }

    fn fused_mul_add<T: Borrow<Self>>(&self, x: T, y: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f16_mulAdd(self.0, x.borrow().0, y.borrow().0) };
        Self(ret)
    }

    fn div<T: Borrow<Self>>(&self, x: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f16_div(self.0, x.borrow().0) };
        Self(ret)
    }

    fn rem<T: Borrow<Self>>(&self, x: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f16_rem(self.0, x.borrow().0) };
        Self(ret)
    }

    fn sqrt(&self, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f16_sqrt(self.0) };
        Self(ret)
    }

    fn eq<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f16_eq(self.0, x.borrow().0) }
    }

    fn lt<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f16_lt(self.0, x.borrow().0) }
    }

    fn le<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f16_le(self.0, x.borrow().0) }
    }

    fn lt_quiet<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f16_lt_quiet(self.0, x.borrow().0) }
    }

    fn le_quiet<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f16_le_quiet(self.0, x.borrow().0) }
    }

    fn eq_signaling<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f16_eq_signaling(self.0, x.borrow().0) }
    }

    fn is_signaling_nan(&self) -> bool {
        unsafe { softfloat_sys::f16_isSignalingNaN(self.0) }
    }

    fn from_u32(x: u32, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::ui32_to_f16(x) };
        Self(ret)
    }

    fn from_u64(x: u64, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::ui64_to_f16(x) };
        Self(ret)
    }

    fn from_i32(x: i32, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::i32_to_f16(x) };
        Self(ret)
    }

    fn from_i64(x: i64, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::i64_to_f16(x) };
        Self(ret)
    }

    fn to_u32(&self, rnd: RoundingMode, exact: bool) -> u32 {
        let ret = unsafe { softfloat_sys::f16_to_ui32(self.0, rnd.to_softfloat(), exact) };
        ret as u32
    }

    fn to_u64(&self, rnd: RoundingMode, exact: bool) -> u64 {
        let ret = unsafe { softfloat_sys::f16_to_ui64(self.0, rnd.to_softfloat(), exact) };
        ret
    }

    fn to_i32(&self, rnd: RoundingMode, exact: bool) -> i32 {
        let ret = unsafe { softfloat_sys::f16_to_i32(self.0, rnd.to_softfloat(), exact) };
        ret as i32
    }

    fn to_i64(&self, rnd: RoundingMode, exact: bool) -> i64 {
        let ret = unsafe { softfloat_sys::f16_to_i64(self.0, rnd.to_softfloat(), exact) };
        ret
    }

    fn to_f16(&self, _rnd: RoundingMode) -> F16 {
        Self::from_bits(self.to_bits())
    }

    fn to_f32(&self, rnd: RoundingMode) -> F32 {
        rnd.set();
        let ret = unsafe { softfloat_sys::f16_to_f32(self.0) };
        F32::from_bits(ret.v)
    }

    fn to_f64(&self, rnd: RoundingMode) -> F64 {
        rnd.set();
        let ret = unsafe { softfloat_sys::f16_to_f64(self.0) };
        F64::from_bits(ret.v)
    }

    #[cfg(not(feature = "concordium"))]
    fn to_f128(&self, rnd: RoundingMode) -> super::F128 {
        rnd.set();
        let ret = unsafe { softfloat_sys::f16_to_f128(self.0) };
        let mut v = 0u128;
        v |= ret.v[0] as u128;
        v |= (ret.v[1] as u128) << 64;
        super::F128::from_bits(v)
    }

    fn round_to_integral(&self, rnd: RoundingMode) -> Self {
        let ret = unsafe { softfloat_sys::f16_roundToInt(self.0, rnd.to_softfloat(), false) };
        Self(ret)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ExceptionFlags;
    use std::cmp::Ordering;

    #[test]
    fn f16_add() {
        let a = 0x1234;
        let b = 0x7654;
        let a0 = F16::from_bits(a);
        let b0 = F16::from_bits(b);
        let d0 = a0.add(b0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F16::from_bits(a);
        let b1 = simple_soft_float::F16::from_bits(b);
        let d1 = a1.add(&b1, Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f16_sub() {
        let a = 0x1234;
        let b = 0x7654;
        let a0 = F16::from_bits(a);
        let b0 = F16::from_bits(b);
        let d0 = a0.sub(b0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F16::from_bits(a);
        let b1 = simple_soft_float::F16::from_bits(b);
        let d1 = a1.sub(&b1, Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f16_mul() {
        let a = 0x1234;
        let b = 0x7654;
        let a0 = F16::from_bits(a);
        let b0 = F16::from_bits(b);
        let d0 = a0.mul(b0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F16::from_bits(a);
        let b1 = simple_soft_float::F16::from_bits(b);
        let d1 = a1.mul(&b1, Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f16_fused_mul_add() {
        let a = 0x1234;
        let b = 0x1234;
        let c = 0x1234;
        let a0 = F16::from_bits(a);
        let b0 = F16::from_bits(b);
        let c0 = F16::from_bits(c);
        let d0 = a0.fused_mul_add(b0, c0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F16::from_bits(a);
        let b1 = simple_soft_float::F16::from_bits(b);
        let c1 = simple_soft_float::F16::from_bits(c);
        let d1 = a1.fused_mul_add(
            &b1,
            &c1,
            Some(simple_soft_float::RoundingMode::TiesToEven),
            None,
        );
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f16_div() {
        let a = 0x7654;
        let b = 0x1234;
        let a0 = F16::from_bits(a);
        let b0 = F16::from_bits(b);
        let d0 = a0.div(b0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F16::from_bits(a);
        let b1 = simple_soft_float::F16::from_bits(b);
        let d1 = a1.div(&b1, Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f16_rem() {
        let a = 0x7654;
        let b = 0x1234;
        let a0 = F16::from_bits(a);
        let b0 = F16::from_bits(b);
        let d0 = a0.rem(b0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F16::from_bits(a);
        let b1 = simple_soft_float::F16::from_bits(b);
        let d1 = a1.ieee754_remainder(&b1, Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f16_sqrt() {
        let a = 0x7654;
        let a0 = F16::from_bits(a);
        let d0 = a0.sqrt(RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F16::from_bits(a);
        let d1 = a1.sqrt(Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f16_compare() {
        let a = F16::from_bits(0x7654);
        let b = F16::from_bits(0x1234);
        let d = a.compare(b);
        assert_eq!(d, Some(Ordering::Greater));

        let a = F16::from_bits(0x1234);
        let b = F16::from_bits(0x7654);
        let d = a.compare(b);
        assert_eq!(d, Some(Ordering::Less));

        let a = F16::from_bits(0x1234);
        let b = F16::from_bits(0x1234);
        let d = a.compare(b);
        assert_eq!(d, Some(Ordering::Equal));
    }

    #[test]
    fn f16_signaling() {
        let a = F16::from_bits(0x7c01);
        let b = F16::from_bits(0x7e01);
        assert_eq!(a.is_signaling_nan(), true);
        assert_eq!(b.is_signaling_nan(), false);

        let mut flag = ExceptionFlags::default();
        flag.set();
        assert_eq!(SoftFloat::eq(&a, a), false);
        flag.get();
        assert_eq!(flag.is_invalid(), true);

        let mut flag = ExceptionFlags::default();
        flag.set();
        assert_eq!(SoftFloat::eq(&b, b), false);
        flag.get();
        assert_eq!(flag.is_invalid(), false);

        let mut flag = ExceptionFlags::default();
        flag.set();
        assert_eq!(a.eq_signaling(a), false);
        flag.get();
        assert_eq!(flag.is_invalid(), true);

        let mut flag = ExceptionFlags::default();
        flag.set();
        assert_eq!(b.eq_signaling(b), false);
        flag.get();
        assert_eq!(flag.is_invalid(), true);
    }

    #[cfg(not(feature = "concordium"))]
    #[test]
    fn from_f32() {
        let a = F16::from_native_f32(0.1);
        assert_eq!(a.to_bits(), 0x2e66);
    }

    #[cfg(not(feature = "concordium"))]
    #[test]
    fn from_f64() {
        let a = F16::from_native_f64(0.1);
        assert_eq!(a.to_bits(), 0x2e66);
    }
}
