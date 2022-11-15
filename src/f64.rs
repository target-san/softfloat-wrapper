use crate::{RoundingMode, SoftFloat, F16, F32};
use softfloat_sys::float64_t;
use std::borrow::Borrow;

/// standard 64-bit float
#[derive(Copy, Clone, Debug)]
pub struct F64(float64_t);

#[cfg(feature = "concordium")]
impl concordium_std::schema::SchemaType for F64 {
    fn get_type() -> concordium_std::schema::Type {
        <<Self as crate::SoftFloat>::Payload as concordium_std::schema::SchemaType>::get_type()
    }
}

#[cfg(feature = "concordium")]
impl concordium_std::Serial for F64 {
    fn serial<W: concordium_std::Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.to_bits().serial(out)
    }
}

#[cfg(feature = "concordium")]
impl concordium_std::Deserial for F64 {
    fn deserial<R: concordium_std::Read>(source: &mut R) -> concordium_std::ParseResult<Self> {
        Ok(Self::from_bits(<Self as crate::SoftFloat>::Payload::deserial(
            source,
        )?))
    }
}

impl Default for F64 {
    fn default() -> Self {
        num_traits::Zero::zero()
    }
}

impl num_traits::Zero for F64 {
    fn zero() -> Self {
        crate::SoftFloat::positive_zero()
    }

    fn is_zero(&self) -> bool {
        crate::SoftFloat::is_zero(self)
    }
}

impl num_traits::One for F64 {
    fn one() -> Self {
        crate::SoftFloat::from_i8(1, crate::DEFAULT_ROUNDING_MODE)
    }
}

impl std::ops::Neg for F64 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        crate::SoftFloat::neg(&self)
    }
}

impl std::ops::Add for F64 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        crate::SoftFloat::add(&self, rhs, crate::DEFAULT_ROUNDING_MODE)
    }
}

impl std::ops::AddAssign for F64 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl std::ops::Sub for F64 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        crate::SoftFloat::sub(&self, rhs, crate::DEFAULT_ROUNDING_MODE)
    }
}

impl std::ops::SubAssign for F64 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl std::ops::Mul for F64 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        crate::SoftFloat::mul(&self, rhs, crate::DEFAULT_ROUNDING_MODE)
    }
}

impl std::ops::MulAssign for F64 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl std::ops::Div for F64 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        crate::SoftFloat::div(&self, rhs, crate::DEFAULT_ROUNDING_MODE)
    }
}

impl std::ops::DivAssign for F64 {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl std::ops::Rem for F64 {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        crate::SoftFloat::rem(&self, rhs, crate::DEFAULT_ROUNDING_MODE)
    }
}

impl std::ops::RemAssign for F64 {
    fn rem_assign(&mut self, rhs: Self) {
        *self = *self % rhs;
    }
}

impl std::cmp::PartialEq for F64 {
    fn eq(&self, other: &Self) -> bool {
        crate::SoftFloat::eq(self, other)
    }
}

impl std::cmp::PartialOrd for F64 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        crate::SoftFloat::compare(self, other)
    }
}

impl SoftFloat for F64 {
    type Payload = u64;

    const MANTISSA_MASK: Self::Payload = 0xf_ffff_ffff_ffff;
    const EXPONENT_MASK: Self::Payload = 0x7ff;
    const MANTISSA_BITS: usize = 52;
    const EXPONENT_BITS: usize = 11;
    const SIGN_OFFSET: usize = 63;
    const EXPONENT_OFFSET: usize = 52;

    #[cfg(not(feature = "concordium"))]
    fn from_native_f32(v: f32) -> Self {
        F32::from_bits(v.to_bits()).to_f64(RoundingMode::TiesToEven)
    }

    #[cfg(not(feature = "concordium"))]
    fn from_native_f64(v: f64) -> Self {
        Self::from_bits(v.to_bits())
    }

    #[inline]
    fn set_payload(&mut self, x: Self::Payload) {
        self.0.v = x;
    }

    #[inline]
    fn from_bits(v: Self::Payload) -> Self {
        Self(float64_t { v })
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
        let ret = unsafe { softfloat_sys::f64_add(self.0, x.borrow().0) };
        Self(ret)
    }

    fn sub<T: Borrow<Self>>(&self, x: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f64_sub(self.0, x.borrow().0) };
        Self(ret)
    }

    fn mul<T: Borrow<Self>>(&self, x: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f64_mul(self.0, x.borrow().0) };
        Self(ret)
    }

    fn fused_mul_add<T: Borrow<Self>>(&self, x: T, y: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f64_mulAdd(self.0, x.borrow().0, y.borrow().0) };
        Self(ret)
    }

    fn div<T: Borrow<Self>>(&self, x: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f64_div(self.0, x.borrow().0) };
        Self(ret)
    }

    fn rem<T: Borrow<Self>>(&self, x: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f64_rem(self.0, x.borrow().0) };
        Self(ret)
    }

    fn sqrt(&self, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f64_sqrt(self.0) };
        Self(ret)
    }

    fn eq<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f64_eq(self.0, x.borrow().0) }
    }

    fn lt<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f64_lt(self.0, x.borrow().0) }
    }

    fn le<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f64_le(self.0, x.borrow().0) }
    }

    fn lt_quiet<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f64_lt_quiet(self.0, x.borrow().0) }
    }

    fn le_quiet<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f64_le_quiet(self.0, x.borrow().0) }
    }

    fn eq_signaling<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f64_eq_signaling(self.0, x.borrow().0) }
    }

    fn is_signaling_nan(&self) -> bool {
        unsafe { softfloat_sys::f64_isSignalingNaN(self.0) }
    }

    fn from_u32(x: u32, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::ui32_to_f64(x) };
        Self(ret)
    }

    fn from_u64(x: u64, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::ui64_to_f64(x) };
        Self(ret)
    }

    fn from_i32(x: i32, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::i32_to_f64(x) };
        Self(ret)
    }

    fn from_i64(x: i64, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::i64_to_f64(x) };
        Self(ret)
    }

    fn to_u32(&self, rnd: RoundingMode, exact: bool) -> u32 {
        let ret = unsafe { softfloat_sys::f64_to_ui32(self.0, rnd.to_softfloat(), exact) };
        ret as u32
    }

    fn to_u64(&self, rnd: RoundingMode, exact: bool) -> u64 {
        let ret = unsafe { softfloat_sys::f64_to_ui64(self.0, rnd.to_softfloat(), exact) };
        ret
    }

    fn to_i32(&self, rnd: RoundingMode, exact: bool) -> i32 {
        let ret = unsafe { softfloat_sys::f64_to_i32(self.0, rnd.to_softfloat(), exact) };
        ret as i32
    }

    fn to_i64(&self, rnd: RoundingMode, exact: bool) -> i64 {
        let ret = unsafe { softfloat_sys::f64_to_i64(self.0, rnd.to_softfloat(), exact) };
        ret
    }

    fn to_f16(&self, rnd: RoundingMode) -> F16 {
        rnd.set();
        let ret = unsafe { softfloat_sys::f64_to_f16(self.0) };
        F16::from_bits(ret.v)
    }

    fn to_f32(&self, rnd: RoundingMode) -> F32 {
        rnd.set();
        let ret = unsafe { softfloat_sys::f64_to_f32(self.0) };
        F32::from_bits(ret.v)
    }

    fn to_f64(&self, _rnd: RoundingMode) -> F64 {
        Self::from_bits(self.to_bits())
    }

    #[cfg(not(feature = "concordium"))]
    fn to_f128(&self, rnd: RoundingMode) -> super::F128 {
        rnd.set();
        let ret = unsafe { softfloat_sys::f64_to_f128(self.0) };
        let mut v = 0u128;
        v |= ret.v[0] as u128;
        v |= (ret.v[1] as u128) << 64;
        super::F128::from_bits(v)
    }

    fn round_to_integral(&self, rnd: RoundingMode) -> Self {
        let ret = unsafe { softfloat_sys::f64_roundToInt(self.0, rnd.to_softfloat(), false) };
        Self(ret)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ExceptionFlags;
    use std::cmp::Ordering;

    #[test]
    fn f64_add() {
        let a = 0x12345678ffffffff;
        let b = 0x76546410aaaaaaaa;
        let a0 = F64::from_bits(a);
        let b0 = F64::from_bits(b);
        let d0 = SoftFloat::add(&a0, b0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F64::from_bits(a);
        let b1 = simple_soft_float::F64::from_bits(b);
        let d1 = a1.add(&b1, Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f64_sub() {
        let a = 0x12345678ffffffff;
        let b = 0x76546410aaaaaaaa;
        let a0 = F64::from_bits(a);
        let b0 = F64::from_bits(b);
        let d0 = SoftFloat::sub(&a0, b0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F64::from_bits(a);
        let b1 = simple_soft_float::F64::from_bits(b);
        let d1 = a1.sub(&b1, Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f64_mul() {
        let a = 0x12345678ffffffff;
        let b = 0x76546410aaaaaaaa;
        let a0 = F64::from_bits(a);
        let b0 = F64::from_bits(b);
        let d0 = SoftFloat::mul(&a0, b0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F64::from_bits(a);
        let b1 = simple_soft_float::F64::from_bits(b);
        let d1 = a1.mul(&b1, Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f64_fused_mul_add() {
        let a = 0x12345678ffffffff;
        let b = 0x12345678aaaaaaaa;
        let c = 0x12345678aaaaaaaa;
        let a0 = F64::from_bits(a);
        let b0 = F64::from_bits(b);
        let c0 = F64::from_bits(c);
        let d0 = a0.fused_mul_add(b0, c0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F64::from_bits(a);
        let b1 = simple_soft_float::F64::from_bits(b);
        let c1 = simple_soft_float::F64::from_bits(c);
        let d1 = a1.fused_mul_add(
            &b1,
            &c1,
            Some(simple_soft_float::RoundingMode::TiesToEven),
            None,
        );
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f64_div() {
        let a = 0x76545678ffffffff;
        let b = 0x12346410aaaaaaaa;
        let a0 = F64::from_bits(a);
        let b0 = F64::from_bits(b);
        let d0 = SoftFloat::div(&a0, b0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F64::from_bits(a);
        let b1 = simple_soft_float::F64::from_bits(b);
        let d1 = a1.div(&b1, Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f64_rem() {
        let a = 0x76545678ffffffff;
        let b = 0x12346410aaaaaaaa;
        let a0 = F64::from_bits(a);
        let b0 = F64::from_bits(b);
        let d0 = SoftFloat::rem(&a0, b0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F64::from_bits(a);
        let b1 = simple_soft_float::F64::from_bits(b);
        let d1 = a1.ieee754_remainder(&b1, Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f64_sqrt() {
        let a = 0x76546410aaaaaaaa;
        let a0 = F64::from_bits(a);
        let d0 = a0.sqrt(RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F64::from_bits(a);
        let d1 = a1.sqrt(Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f64_compare() {
        let a = F64::from_bits(0x76546410ffffffff);
        let b = F64::from_bits(0x12345678aaaaaaaa);
        let d = a.compare(b);
        assert_eq!(d, Some(Ordering::Greater));

        let a = F64::from_bits(0x12345678ffffffff);
        let b = F64::from_bits(0x76546410aaaaaaaa);
        let d = a.compare(b);
        assert_eq!(d, Some(Ordering::Less));

        let a = F64::from_bits(0x12345678aaaaaaaa);
        let b = F64::from_bits(0x12345678aaaaaaaa);
        let d = a.compare(b);
        assert_eq!(d, Some(Ordering::Equal));
    }

    #[test]
    fn f64_signaling() {
        let a = F64::from_bits(0x7ff0000000000001);
        let b = F64::from_bits(0x7ff8000000000001);
        assert_eq!(a.is_signaling_nan(), true);
        assert_eq!(b.is_signaling_nan(), false);

        let mut flag = ExceptionFlags::default();
        flag.set();
        assert_eq!(a == a, false);
        flag.get();
        assert_eq!(flag.is_invalid(), true);

        let mut flag = ExceptionFlags::default();
        flag.set();
        assert_eq!(b == b, false);
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
        let a = F64::from_native_f32(0.1);
        assert_eq!(a.to_bits(), 0x3fb99999a0000000);
    }

    #[cfg(not(feature = "concordium"))]
    #[test]
    fn from_f64() {
        let a = F64::from_native_f64(0.1);
        assert_eq!(a.to_bits(), 0x3fb999999999999a);
    }
}
