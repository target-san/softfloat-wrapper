use crate::{RoundingMode, SoftFloat, F16, F64};
use softfloat_sys::float32_t;
use std::borrow::Borrow;

/// standard 32-bit float
#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
pub struct F32(float32_t);

impl F32 {
    pub const fn from_bits(v: u32) -> Self {
        Self(float32_t { v })
    }

    pub const fn to_bits(&self) -> u32 {
        self.0.v
    }
}

impl SoftFloat for F32 {
    type Payload = u32;

    const MANTISSA_MASK: Self::Payload = 0x7f_ffff;
    const EXPONENT_MASK: Self::Payload = 0xff;
    const MANTISSA_BITS: usize = 23;
    const EXPONENT_BITS: usize = 8;
    const SIGN_OFFSET: usize = 31;
    const EXPONENT_OFFSET: usize = 23;

    #[cfg(feature = "native-float")]
    fn from_native_f32(v: f32) -> Self {
        Self::from_bits(v.to_bits())
    }

    #[cfg(feature = "native-float")]
    fn from_native_f64(v: f64) -> Self {
        F64::from_bits(v.to_bits()).to_f32(RoundingMode::TiesToEven)
    }

    #[inline]
    fn set_payload(&mut self, x: Self::Payload) {
        self.0.v = x;
    }

    #[inline]
    fn from_bits(v: Self::Payload) -> Self {
        F32::from_bits(v)
    }

    #[inline]
    fn to_bits(&self) -> Self::Payload {
        F32::to_bits(self)
    }

    #[inline]
    fn bits(&self) -> Self::Payload {
        self.to_bits()
    }

    fn add<T: Borrow<Self>>(&self, x: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f32_add(self.0, x.borrow().0) };
        Self(ret)
    }

    fn sub<T: Borrow<Self>>(&self, x: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f32_sub(self.0, x.borrow().0) };
        Self(ret)
    }

    fn mul<T: Borrow<Self>>(&self, x: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f32_mul(self.0, x.borrow().0) };
        Self(ret)
    }

    fn fused_mul_add<T: Borrow<Self>>(&self, x: T, y: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f32_mulAdd(self.0, x.borrow().0, y.borrow().0) };
        Self(ret)
    }

    fn div<T: Borrow<Self>>(&self, x: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f32_div(self.0, x.borrow().0) };
        Self(ret)
    }

    fn rem<T: Borrow<Self>>(&self, x: T, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f32_rem(self.0, x.borrow().0) };
        Self(ret)
    }

    fn sqrt(&self, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::f32_sqrt(self.0) };
        Self(ret)
    }

    fn eq<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f32_eq(self.0, x.borrow().0) }
    }

    fn lt<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f32_lt(self.0, x.borrow().0) }
    }

    fn le<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f32_le(self.0, x.borrow().0) }
    }

    fn lt_quiet<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f32_lt_quiet(self.0, x.borrow().0) }
    }

    fn le_quiet<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f32_le_quiet(self.0, x.borrow().0) }
    }

    fn eq_signaling<T: Borrow<Self>>(&self, x: T) -> bool {
        unsafe { softfloat_sys::f32_eq_signaling(self.0, x.borrow().0) }
    }

    fn is_signaling_nan(&self) -> bool {
        unsafe { softfloat_sys::f32_isSignalingNaN(self.0) }
    }

    fn from_u32(x: u32, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::ui32_to_f32(x) };
        Self(ret)
    }

    fn from_u64(x: u64, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::ui64_to_f32(x) };
        Self(ret)
    }

    fn from_i32(x: i32, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::i32_to_f32(x) };
        Self(ret)
    }

    fn from_i64(x: i64, rnd: RoundingMode) -> Self {
        rnd.set();
        let ret = unsafe { softfloat_sys::i64_to_f32(x) };
        Self(ret)
    }

    fn to_u32(&self, rnd: RoundingMode, exact: bool) -> u32 {
        let ret = unsafe { softfloat_sys::f32_to_ui32(self.0, rnd.to_softfloat(), exact) };
        ret as u32
    }

    fn to_u64(&self, rnd: RoundingMode, exact: bool) -> u64 {
        let ret = unsafe { softfloat_sys::f32_to_ui64(self.0, rnd.to_softfloat(), exact) };
        ret
    }

    fn to_i32(&self, rnd: RoundingMode, exact: bool) -> i32 {
        let ret = unsafe { softfloat_sys::f32_to_i32(self.0, rnd.to_softfloat(), exact) };
        ret as i32
    }

    fn to_i64(&self, rnd: RoundingMode, exact: bool) -> i64 {
        let ret = unsafe { softfloat_sys::f32_to_i64(self.0, rnd.to_softfloat(), exact) };
        ret
    }

    fn to_f16(&self, rnd: RoundingMode) -> F16 {
        rnd.set();
        let ret = unsafe { softfloat_sys::f32_to_f16(self.0) };
        F16::from_bits(ret.v)
    }

    fn to_f32(&self, _rnd: RoundingMode) -> F32 {
        Self::from_bits(self.to_bits())
    }

    fn to_f64(&self, rnd: RoundingMode) -> F64 {
        rnd.set();
        let ret = unsafe { softfloat_sys::f32_to_f64(self.0) };
        F64::from_bits(ret.v)
    }

    #[cfg(feature = "f128")]
    fn to_f128(&self, rnd: RoundingMode) -> super::F128 {
        rnd.set();
        let ret = unsafe { softfloat_sys::f32_to_f128(self.0) };
        let mut v = 0u128;
        v |= ret.v[0] as u128;
        v |= (ret.v[1] as u128) << 64;
        super::F128::from_bits(v)
    }

    fn round_to_integral(&self, rnd: RoundingMode) -> Self {
        let ret = unsafe { softfloat_sys::f32_roundToInt(self.0, rnd.to_softfloat(), false) };
        Self(ret)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ExceptionFlags;
    use std::cmp::Ordering;

    #[test]
    fn f32_add() {
        let a = 0x12345678;
        let b = 0x76543210;
        let a0 = F32::from_bits(a);
        let b0 = F32::from_bits(b);
        let d0 = SoftFloat::add(&a0, b0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F32::from_bits(a);
        let b1 = simple_soft_float::F32::from_bits(b);
        let d1 = a1.add(&b1, Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f32_sub() {
        let a = 0x12345678;
        let b = 0x76543210;
        let a0 = F32::from_bits(a);
        let b0 = F32::from_bits(b);
        let d0 = SoftFloat::sub(&a0, b0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F32::from_bits(a);
        let b1 = simple_soft_float::F32::from_bits(b);
        let d1 = a1.sub(&b1, Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f32_mul() {
        let a = 0x12345678;
        let b = 0x76543210;
        let a0 = F32::from_bits(a);
        let b0 = F32::from_bits(b);
        let d0 = SoftFloat::mul(&a0, b0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F32::from_bits(a);
        let b1 = simple_soft_float::F32::from_bits(b);
        let d1 = a1.mul(&b1, Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f32_fused_mul_add() {
        let a = 0x12345678;
        let b = 0x12345678;
        let c = 0x12345678;
        let a0 = F32::from_bits(a);
        let b0 = F32::from_bits(b);
        let c0 = F32::from_bits(c);
        let d0 = a0.fused_mul_add(b0, c0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F32::from_bits(a);
        let b1 = simple_soft_float::F32::from_bits(b);
        let c1 = simple_soft_float::F32::from_bits(c);
        let d1 = a1.fused_mul_add(
            &b1,
            &c1,
            Some(simple_soft_float::RoundingMode::TiesToEven),
            None,
        );
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f32_div() {
        let a = 0x76545678;
        let b = 0x12343210;
        let a0 = F32::from_bits(a);
        let b0 = F32::from_bits(b);
        let d0 = SoftFloat::div(&a0, b0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F32::from_bits(a);
        let b1 = simple_soft_float::F32::from_bits(b);
        let d1 = a1.div(&b1, Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f32_rem() {
        let a = 0x76545678;
        let b = 0x12343210;
        let a0 = F32::from_bits(a);
        let b0 = F32::from_bits(b);
        let d0 = SoftFloat::rem(&a0, b0, RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F32::from_bits(a);
        let b1 = simple_soft_float::F32::from_bits(b);
        let d1 = a1.ieee754_remainder(&b1, Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f32_sqrt() {
        let a = 0x76543210;
        let a0 = F32::from_bits(a);
        let d0 = a0.sqrt(RoundingMode::TiesToEven);
        let a1 = simple_soft_float::F32::from_bits(a);
        let d1 = a1.sqrt(Some(simple_soft_float::RoundingMode::TiesToEven), None);
        assert_eq!(d0.to_bits(), *d1.bits());
    }

    #[test]
    fn f32_compare() {
        let a = F32::from_bits(0x76543210);
        let b = F32::from_bits(0x12345678);
        let d = a.compare(b);
        assert_eq!(d, Some(Ordering::Greater));

        let a = F32::from_bits(0x12345678);
        let b = F32::from_bits(0x76543210);
        let d = a.compare(b);
        assert_eq!(d, Some(Ordering::Less));

        let a = F32::from_bits(0x12345678);
        let b = F32::from_bits(0x12345678);
        let d = a.compare(b);
        assert_eq!(d, Some(Ordering::Equal));
    }

    #[test]
    fn f32_signaling() {
        let a = F32::from_bits(0x7f800001);
        let b = F32::from_bits(0x7fc00001);
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

    #[cfg(feature = "native-float")]
    #[test]
    fn from_f32() {
        let a = F32::from_native_f32(0.1);
        assert_eq!(a.to_bits(), 0x3dcccccd);
    }

    #[cfg(feature = "native-float")]
    #[test]
    fn from_f64() {
        let a = F32::from_native_f64(0.1);
        assert_eq!(a.to_bits(), 0x3dcccccd);
    }
}
