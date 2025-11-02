#![cfg_attr(not(test), no_std)]

use core::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Deref, DerefMut, Not,
};

use cmov::Cmov;

pub use cnti_derive::{CtEq, CtOrd, CtPartialEq, CtSelect};

mod black_box;
pub use black_box::BlackBox;

mod option;
pub use option::CtOption;

/// The CtBool struct represents a boolean that is used for "branching" in branchless,
/// constant-time programs
///
/// It aims to prevent LLVM from using its knowledge of the fact that a bool is either `0` or `1`
/// to re-insert branches in otherwise branchless code. Constructing a CtBool from
/// `CtBool::protect(my_boolean)` passes the boolean through an optimization barrier that is a
/// best-effort attempt to prevent such optimizations. It is very similar to
/// [`subtle::Choice`](https://docs.rs/subtle/2.6.1/subtle/struct.Choice.html).
///
/// # Example usage:
///
/// ```no_run
/// use cnti::{CtBool, CtPartialEq, CtSelect, CtSelectExt};
/// # let a: u8 = 12;
/// # let b = 13;
/// # let mut c = 15;
///
///
/// // equal is a CtBool
/// let a_equal_b = a.ct_eq(&b);
///
/// // set c to 0 if  a == b
/// c.ct_replace_if(&0, a_equal_b);
///
/// ```
#[derive(Copy, Clone, Default, CtEq, CtSelect)]
#[repr(transparent)]
pub struct CtBool(BlackBox<u8>);

impl core::fmt::Debug for CtBool {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "CtBool")
    }
}

impl CtOrd for CtBool {
    #[inline]
    fn ct_gt(&self, other: &Self) -> CtBool {
        *self & !*other
    }
}

impl CtPartialEq for CtBool {
    #[inline]
    fn ct_eq(&self, rhs: &CtBool) -> CtBool {
        !(*self ^ *rhs)
    }
}

impl CtBool {
    pub const TRUE: CtBool = CtBool(BlackBox::protect(true as u8));
    pub const FALSE: CtBool = CtBool(BlackBox::protect(false as u8));

    #[inline]
    /// Reveals the underlying boolean, removing any timing protections.
    /// This should generally be performed only once the value is safe to reveal
    pub const fn expose(self) -> bool {
        self.to_u8() != 0
    }

    #[inline]
    /// Yields the underlying u8 (which is guaranteed to be either 0 or 1, though the optimizer
    /// should be unaware of this fact)
    ///
    /// Library users should nonetheless be careful with how they use this value if they choose to
    /// expose it.
    pub const fn to_u8(self) -> u8 {
        self.0.expose_const()
    }

    #[inline]
    const fn from_u8(inner: u8) -> Self {
        debug_assert!(inner == 0 || inner == 1);
        Self(BlackBox::protect(inner))
    }
}

impl BitAnd for CtBool {
    type Output = CtBool;
    #[inline]
    fn bitand(self, rhs: CtBool) -> CtBool {
        CtBool::from_u8(self.to_u8() & rhs.to_u8())
    }
}

impl BitAndAssign for CtBool {
    #[inline]
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl BitOr for CtBool {
    type Output = CtBool;
    #[inline]
    fn bitor(self, rhs: CtBool) -> CtBool {
        CtBool::from_u8(self.to_u8() | rhs.to_u8())
    }
}

impl BitXor for CtBool {
    type Output = CtBool;
    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        CtBool::from_u8(self.to_u8() ^ rhs.to_u8())
    }
}

impl BitXorAssign for CtBool {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs
    }
}

impl BitOrAssign for CtBool {
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl Not for CtBool {
    type Output = CtBool;
    #[inline]
    fn not(self) -> Self::Output {
        CtBool::from_u8(1u8 & (!self.to_u8()))
    }
}

pub trait CtPartialEq {
    fn ct_eq(&self, other: &Self) -> CtBool;

    #[inline]
    fn ct_neq(&self, other: &Self) -> CtBool {
        !self.ct_eq(other)
    }
}

pub trait CtEq: CtPartialEq {}

impl<const N: usize, T: CtPartialEq> CtPartialEq for [T; N] {
    #[inline]
    fn ct_eq(&self, rhs: &Self) -> CtBool {
        util::ct_all(self, rhs, CtPartialEq::ct_eq)
    }
}

impl<const N: usize, T: CtEq> CtEq for [T; N] {}

impl<const N: usize, T: CtOrd> CtOrd for [T; N] {
    #[inline]
    fn ct_gt(&self, other: &Self) -> CtBool {
        util::ct_all(self, other, CtOrd::ct_gt)
    }

    #[inline]
    fn ct_lt(&self, other: &Self) -> CtBool {
        util::ct_all(self, other, CtOrd::ct_lt)
    }

    #[inline]
    fn ct_leq(&self, other: &Self) -> CtBool {
        util::ct_all(self, other, CtOrd::ct_leq)
    }

    #[inline]
    fn ct_geq(&self, other: &Self) -> CtBool {
        util::ct_all(self, other, CtOrd::ct_geq)
    }
}

pub trait CtOrd: CtEq {
    fn ct_gt(&self, other: &Self) -> CtBool;

    #[inline]
    fn ct_leq(&self, other: &Self) -> CtBool {
        !self.ct_gt(other)
    }

    #[inline]
    fn ct_lt(&self, other: &Self) -> CtBool {
        other.ct_gt(self)
    }

    #[inline]
    fn ct_geq(&self, other: &Self) -> CtBool {
        !self.ct_lt(other)
    }

    #[inline]
    fn ct_max(&self, other: &Self) -> Self
    where
        Self: CtSelect,
    {
        Self::ct_select(self.ct_gt(other), self, other)
    }

    #[inline]
    fn ct_min(&self, other: &Self) -> Self
    where
        Self: CtSelect,
    {
        Self::ct_select(self.ct_gt(other), self, other)
    }

    #[inline]
    fn ct_clamp(&self, min: &Self, max: &Self) -> Self
    where
        Self: CtSelect,
    {
        self.ct_max(min).ct_min(max)
    }
}

/// Given the bit-width `$bit_width` and the corresponding primitive
/// unsigned and signed types `$t_u` and `$t_i` respectively, generate
/// an `ConstantTimeEq` implementation.
macro_rules! impl_int_no_select {
    ($t_u:ty, $t_i:ty) => {
        impl CtPartialEq for $t_u {
            #[inline]
            fn ct_eq(&self, other: &$t_u) -> CtBool {
                // x == 0 if and only if self == other
                let x = self ^ other;

                // If x == 0, then x and -x are both equal to zero;
                // otherwise, one or both will have its high bit set.
                let y = (x | x.wrapping_neg()) >> (<$t_u>::BITS - 1);

                // Result is the opposite of the high bit (now shifted to low).
                CtBool::from_u8((y ^ 1) as u8)
            }
        }

        impl CtEq for $t_u {}

        impl CtPartialEq for $t_i {
            #[inline]
            fn ct_eq(&self, other: &$t_i) -> CtBool {
                // Bitcast to unsigned and call that implementation.
                (*self as $t_u).ct_eq(&(*other as $t_u))
            }
        }

        impl CtOrd for $t_u {
            fn ct_gt(&self, other: &$t_u) -> CtBool {
                let a = *self;
                let b = *other;
                let diff = b.wrapping_sub(a);
                let res = (((!b) & a) | ((!(a ^ b)) & diff)) >> (<$t_u>::BITS - 1);
                CtBool::from_u8(res as u8)

                //CtBool::from_u8(((*self).wrapping_sub(*other) >> (<$t_u>::BITS - 1)) as u8)
                //let gtb = self & !other; // All the bits in self that are greater than their corresponding bits in other.
                //let mut ltb = !self & other; // All the bits in self that are less than their corresponding bits in other.
                //let mut pow = 1;

                //// Less-than operator is okay here because it's dependent on the bit-width.
                //while pow < <$t_u>::BITS {
                //    ltb |= ltb >> pow; // Bit-smear the highest set bit to the right.
                //    pow += pow;
                //}
                //let mut bit = gtb & !ltb; // Select the highest set bit.
                //let mut pow = 1;

                //while pow < <$t_u>::BITS {
                //    bit |= bit >> pow; // Shift it to the right until we end up with either 0 or 1.
                //    pow += pow;
                //}
                //// XXX We should possibly do the above flattening to 0 or 1 in the
                ////     Choice constructor rather than making it a debug error?
                //CtBool::from_u8((bit & 1) as u8)
            }
        }

        impl CtEq for $t_i {}

        impl CtOrd for $t_i {
            fn ct_gt(&self, other: &Self) -> CtBool {
                let sign_mask = 1 << (<$t_i>::BITS - 1);
                let a = (*self as $t_u) ^ sign_mask;
                let b = (*other as $t_u) ^ sign_mask;
                a.ct_gt(&b)
                //let lt_unsigned = CtBool::from_u8(
                //    (((self_abs
                //        ^ ((self_abs ^ other_abs)
                //            | ((self_abs.wrapping_sub(other_abs)) ^ other_abs)))
                //        >> (<$t_u>::BITS - 1))
                //        & 1) as u8,
                //);
                //let sign_diff = self_sign ^ other_sign;
                //let flip = CtSelect::ct_select(sign_self, sign_diff, !sign_diff);
                //CtSelect::ct_select(other_sign ^ self_sign, &!self_sign, &self_abs.unsigned_g)
            }
        }
    };
}

macro_rules! impl_int {
    ($t_u:ty, $t_i:ty) => {
        impl CtSelect for $t_u {
            #[inline]
            fn ct_select(choice: CtBool, then: &Self, else_: &Self) -> Self {
                let mut res = *else_;
                res.cmovnz(then, choice.to_u8());
                res
            }
        }

        impl CtSelect for $t_i {
            #[inline]
            fn ct_select(choice: CtBool, then: &Self, else_: &Self) -> Self {
                let then = *then as $t_u;
                let else_ = *else_ as $t_u;
                CtSelect::ct_select(choice, &then, &else_) as $t_i
            }
        }
        impl_int_no_select!($t_u, $t_i);
    };
}

impl_int!(u8, i8);
impl_int!(u16, i16);
impl_int!(u32, i32);
impl_int!(u64, i64);
impl_int!(u128, i128);
impl_int_no_select!(usize, isize);

// these annoyingly don't have implementations in the cmov crate, pending that we just use the
// portable fallback
impl CtSelect for usize {
    #[inline]
    fn ct_select(choice: CtBool, then: &Self, else_: &Self) -> Self {
        let mask = -(choice.to_u8() as isize) as usize;
        else_ ^ (mask & (else_ ^ then))
    }
}

// these annoyingly don't have implementations in the cmov crate, pending that we just use the
// portable fallback
impl CtSelect for isize {
    #[inline]
    fn ct_select(choice: CtBool, then: &Self, else_: &Self) -> Self {
        let mask = -(choice.to_u8() as isize);
        else_ ^ (mask & (else_ ^ then))
    }
}

/// Constant time selection based on a [`CtBool`].
///
///
/// Implementors of this trait additionally get a blanket implementation for [`CtSelectExt`] which
/// provides conditional assignment, swapping, etc.
pub trait CtSelect: Sized {
    fn ct_select(choice: CtBool, then: &Self, else_: &Self) -> Self;
}

/// Extension trait for [`CtSelect`] that provides additional utility.
///
/// Blanket implemented for all types that implement [`CtSelect`]
pub trait CtSelectExt: CtSelect {
    #[inline]
    /// Conditionally assigns `other` to `self` returning whatever the original value of `self`
    /// was. In other words, `x.ct_replace_if(&y, choice)` is the constant-time equivalent of
    /// ```text
    /// if choice.expose() {
    ///     core::mem::replace(&mut x, y)
    /// }
    /// ```
    /// ### Usage:
    ///
    /// ```
    /// # use cnti::{CtBool, CtSelectExt};
    /// let mut x = 0_u32;
    /// let y = 1;
    ///
    /// let old_x = x.ct_replace_if(&y, CtBool::TRUE);
    ///
    /// assert_eq!(old_x, 0);
    /// assert_eq!(x, y);
    ///
    ///
    /// let mut a = 0_u32;
    /// let b = 1;
    ///
    /// let old_a = a.ct_replace_if(&b, CtBool::FALSE);
    ///
    /// assert_eq!(old_a, 0);
    /// assert_eq!(old_a, a);
    /// ```
    ///
    fn ct_replace_if(&mut self, other: &Self, choice: CtBool) -> Self {
        core::mem::replace(self, Self::ct_select(choice, other, self))
    }

    /// Conditionally swaps `other` with `self`
    /// In other words, x.ct_swap_if(&mut y, choice)` is the constant-time equivalent of
    /// ```text
    /// if choice.expose() {
    ///     core::mem::swap(&mut x, &mut y);
    /// }
    /// ```
    /// ### Usage:
    /// ```
    /// # use cnti::{CtBool, CtSelectExt};
    /// let mut x = 0_u32;
    /// let mut y = 1;
    ///
    /// x.ct_swap_if(&mut y, CtBool::TRUE);
    ///
    /// assert_eq!(x, 1);
    /// assert_eq!(y, 0);
    ///
    ///
    /// let mut a = 0_u32;
    /// let mut b = 1;
    ///
    /// a.ct_swap_if(&mut b, CtBool::FALSE);
    ///
    /// assert_eq!(a, 0);
    /// assert_eq!(b, 1);
    ///
    #[inline]
    fn ct_swap_if(&mut self, other: &mut Self, choice: CtBool) {
        let old_self = self.ct_replace_if(other, choice);
        other.ct_replace_if(&old_self, choice);
    }

    /// Conditionally assigns `self` to `Self::default()` returning whatever the original value of `self`
    /// was. In other words, `x.ct_take_if(choice)` is the constant-time equivalent of
    /// ```text
    /// if choice.expose() {
    ///     core::mem::take(&mut x)
    /// }
    /// ```
    ///
    /// ### Usage:
    /// ```
    /// # use cnti::{CtBool, CtSelectExt};
    /// let mut x = 1_u32;
    /// x.ct_take_if(CtBool::TRUE);
    ///
    /// assert_eq!(x, 0);
    ///
    ///
    /// let mut a = 1_u32;
    ///
    /// a.ct_take_if(CtBool::FALSE);
    ///
    /// assert_eq!(a, 1);
    ///
    #[inline]
    fn ct_take_if(&mut self, choice: CtBool) -> Self
    where
        Self: Default,
    {
        self.ct_replace_if(&Self::default(), choice)
    }
}

impl<T: CtSelect> CtSelectExt for T {}

impl CtSelect for core::cmp::Ordering {
    #[inline]
    fn ct_select(choice: CtBool, then: &Self, else_: &Self) -> Self {
        let then = *then as i8;
        let else_ = *else_ as i8;
        let res = i8::ct_select(choice, &then, &else_);

        // # SAFETY: res is guaranteed to be in {-1, 0, 1} because it is either a or b which were
        // originally orderings
        unsafe { util::i8_to_ordering(res) }
    }
}

impl<T: CtSelect, const N: usize> CtSelect for [T; N] {
    #[inline]
    fn ct_select(choice: CtBool, then: &[T; N], else_: &[T; N]) -> Self {
        util::arr_combine(then, else_, |t_elem, e_elem| {
            CtSelect::ct_select(choice, t_elem, e_elem)
        })
    }
}

/// Unlike [T; N], &[T] does not implement [`CtEq`]/[`CtPartialEq`] and [`CtOrd`] because the two
/// slices being compared might be of different lengths which would leak information about whether
/// the two operands have identical types.
///
/// `&PublicLenSlice<T>` is effectively an alias for `&[T]` that allows users to explicitly opt-in
/// to this short-circuiting behavior. Note that the [`CtPartialEq`] implementation for this type
/// still uses [`CtPartialEq::ct_eq`] to compare the lengths. However, if they are not equal, the
/// implementation will return early.
#[repr(transparent)]
pub struct PublicLenSlice<T>(pub [T]);

impl<T> PublicLenSlice<T> {
    pub fn from_slice(slice: &[T]) -> &Self {
        // # SAFETY:
        // This is safe because #[repr(transparent)]
        let ptr = slice as *const [T] as *const _;

        unsafe { &*ptr }
    }

    pub fn from_mut_slice(slice: &mut [T]) -> &mut Self {
        // # SAFETY:
        // This is safe because #[repr(transparent)]
        let ptr = slice as *mut [T] as *mut _;

        unsafe { &mut *ptr }
    }
}

impl<T> core::fmt::Debug for &PublicLenSlice<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "PublicLenSlice")
    }
}

impl<'a, T> From<&'a [T]> for &'a PublicLenSlice<T> {
    fn from(value: &'a [T]) -> Self {
        PublicLenSlice::from_slice(value)
    }
}

impl<'a, T> From<&'a mut [T]> for &'a mut PublicLenSlice<T> {
    fn from(value: &'a mut [T]) -> Self {
        PublicLenSlice::from_mut_slice(value)
    }
}

impl<T> Deref for PublicLenSlice<T> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for PublicLenSlice<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T, U> AsRef<T> for PublicLenSlice<U>
where
    T: ?Sized,
    <PublicLenSlice<U> as Deref>::Target: AsRef<T>,
{
    fn as_ref(&self) -> &T {
        self.deref().as_ref()
    }
}

impl<T, U> AsMut<T> for PublicLenSlice<U>
where
    T: ?Sized,
    <PublicLenSlice<U> as Deref>::Target: AsMut<T>,
{
    fn as_mut(&mut self) -> &mut T {
        self.deref_mut().as_mut()
    }
}

impl<T: CtPartialEq> CtPartialEq for PublicLenSlice<T> {
    #[inline]
    fn ct_eq(&self, rhs: &Self) -> CtBool {
        // The contract here is that the length is public so we could just do !=
        // the point is here i want people to have to explicitly opt in to potential leakage when
        // comparing slices, but we don't actually have to fully leak the length
        // this does leak if one is longer though
        if self.len().ct_neq(&rhs.len()).expose() {
            return CtBool::FALSE;
        }

        util::ct_all(self, rhs, CtPartialEq::ct_eq)
    }
}

impl<T: CtEq> CtEq for PublicLenSlice<T> {}

mod util {
    use super::CtBool;
    // this will leak min(lhs.len(), rhs.len())!
    pub(crate) fn ct_all<T>(lhs: &[T], rhs: &[T], f: impl Fn(&T, &T) -> CtBool) -> CtBool {
        lhs.iter()
            .zip(rhs)
            .fold(CtBool::TRUE, |acc, (l, r)| acc & f(l, r))
    }

    // this will leak min(lhs.len(), rhs.len())
    #[allow(unused)]
    pub(crate) fn ct_any<T>(lhs: &[T], rhs: &[T], f: impl Fn(&T, &T) -> CtBool) -> CtBool {
        lhs.iter()
            .zip(rhs)
            .fold(CtBool::FALSE, |acc, (l, r)| acc | f(l, r))
    }

    // Takes two arrays of size n and produces a new array of size n whose ith element is f(lhs[i],
    // rhs[i])
    pub(crate) fn arr_combine<T, const N: usize, U>(
        lhs: &[T; N],
        rhs: &[T; N],
        f: impl Fn(&T, &T) -> U,
    ) -> [U; N] {
        // compiler is smart enough to get rid of bounds checks here!
        // maybe can just get rid of this function
        core::array::from_fn(|i| f(&lhs[i], &rhs[i]))
    }

    // # SAFETY: x must be in {-1, 0, 1}
    pub(crate) unsafe fn i8_to_ordering(x: i8) -> core::cmp::Ordering {
        debug_assert!(x == -1 || x == 0 || x == 1);

        let res_ptr = &raw const x as *const core::cmp::Ordering;
        // # SAFETY: this is safe because core::cmp::Ordering is repr(i8) with all variants in the
        // range {-1, 0, 1}. Per the safety contract of this function, x in {-1, 0, 1}
        unsafe { *res_ptr }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use paste::paste;
    use quickcheck_macros::quickcheck;

    macro_rules! test_ct_select {
        ($($t:path),*) => {
            $(paste! {
                #[quickcheck]
                fn [<test_ct_select_$t>](select: bool, a: $t, b: $t) {
                    assert_eq!(
                        CtSelect::ct_select(CtBool(BlackBox::protect(select as u8)), &a, &b),
                        if select { a } else { b }
                    );
                }

            })*
        };
    }

    extern crate std;

    macro_rules! test_ct_equal {
        ($($t:path),*) => {
            $(paste! {
                #[quickcheck]
                fn [<test_ct_eq_$t>](a: $t, b: $t) {
                    assert_eq!(a.ct_eq(&a).expose(), true);
                    assert_eq!(
                        a.ct_eq(&b).expose(),
                        a == b
                    );
                }


            })*
        };
    }

    macro_rules! test_ct_ord {
        ($($t:path),*) => {
            $(paste! {
                #[quickcheck]
                fn [<test_ct_ord_$t>](a: $t, b: $t) {
                    println!("{a}, {b}");
                    assert_eq!(a.ct_gt(&b).expose(), a > b, "{a} > {b}");
                    assert_eq!(a.ct_lt(&b).expose(), a < b, "{a} < {b}");
                    assert_eq!(a.ct_leq(&b).expose(), a <= b, "{a} <= {b}");
                    assert_eq!(a.ct_geq(&b).expose(), a >= b, "{a} >= {b}");

                    let inc_a = a.wrapping_add(1);
                    assert_eq!(a.ct_gt(&inc_a).expose(), a > inc_a);
                    assert_eq!(a.ct_lt(&inc_a).expose(), a < inc_a);
                    assert_eq!(a.ct_leq(&inc_a).expose(), a <= inc_a);
                    assert_eq!(a.ct_geq(&inc_a).expose(), a >= inc_a);
                }
            })*
        };
    }

    // including usize and isize here because they don't use the cmov crate
    // so their implementation is different
    test_ct_select!(
        i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, isize, usize
    );
    test_ct_equal!(i8, u8, i16, u16, i32, u32, i64, u64, i128, u128);

    test_ct_ord!(u8, i8, i16, u16, i32, u32, i64, u64, i128, u128);
}
