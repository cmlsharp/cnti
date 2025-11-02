#![cfg_attr(not(test), no_std)]

use core::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Deref, DerefMut, Not,
};

use cmov::Cmov;

pub use cnti_derive::{CtEq, CtOrd, CtSelect};

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
/// use cnti::{CtBool, CtEq, CtSelect, CtSelectExt};
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
#[derive(Copy, Clone, Default, CtSelect)]
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

impl CtEq for CtBool {
    #[inline]
    fn ct_eq(&self, rhs: &CtBool) -> CtBool {
        !(*self ^ *rhs)
    }
}

impl CtBool {
    pub const TRUE: CtBool = CtBool(BlackBox::protect(true as u8));
    pub const FALSE: CtBool = CtBool(BlackBox::protect(false as u8));

    #[inline]
    pub const fn protect(b: bool) -> Self {
        CtBool::protect_u8(b as u8)
    }

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

    /// Perform a constant time selection via method chain syntax instead of calling
    /// [`CtSelect::ct_select`].
    ///
    ///
    /// ```
    /// # use cnti::{CtBool, CtSelect, CtEq};
    /// # let x = 10i32;
    /// # let y = 11;
    /// # let a = 12;
    /// # let b = 13;
    ///
    /// let result = x.ct_eq(&y).if_true(&a).else_(&b);
    /// let equivalent = CtSelect::ct_select(x.ct_eq(&y), &a, &b);
    ///
    /// assert_eq!(result, equivalent)
    /// ```
    pub fn if_true<'a, T: CtSelect>(&self, then: &'a T) -> CtIf<'a, T, true> {
        CtIf::<'_, _, true> { cond: *self, then }
    }

    /// Perform a constant time selection via method chain syntax instead of calling
    /// [`CtSelect::ct_select`].
    ///
    ///
    /// ```
    /// # use cnti::{CtBool, CtSelect, CtEq};
    /// # let x = 10i32;
    /// # let y = 11;
    /// # let a = 12;
    /// # let b = 13;
    ///
    /// let result = x.ct_eq(&y).if_false(&a).else_(&b);
    /// let equivalent = CtSelect::ct_select(x.ct_eq(&y), &b, &a);
    ///
    /// assert_eq!(result, equivalent)
    /// ```
    pub fn if_false<'a, T: CtSelect>(&self, then: &'a T) -> CtIf<'a, T, false> {
        CtIf::<'_, _, false> { cond: *self, then }
    }

    #[inline]
    // TODO: Decide whether we want to make this public
    // I'm kinda inclined to say no. If you have a u8, you can always
    // construct a CtBool via CtSelect::ct_select(my_u8.ct_eq(&0), CtBool::FALSE, CtBool::TRUE)
    const fn protect_u8(inner: u8) -> Self {
        debug_assert!(inner == 0 || inner == 1);
        Self(BlackBox::protect(inner))
    }

    // this function should only ever be called when the optimizer should be unable to tell that
    // the u8 must be either 0 or 1
    const fn from_raw_unchecked(inner: u8) -> Self {
        debug_assert!(inner == 0 || inner == 1);
        Self(BlackBox::from_raw_unchecked(inner))
    }
}

/// Represents an incomplete [`CtSelect`] expression.
/// See the documentation for [`CtBool::if_true`]/[`CtBool::if_false`].
pub struct CtIf<'a, T, const TRUE: bool> {
    cond: CtBool,
    then: &'a T,
}

impl<T, const TRUE: bool> CtIf<'_, T, TRUE> {
    /// Perform the `ct_select` by providing the alternative value
    pub fn else_(self, else_: &T) -> T
    where
        T: CtSelect,
    {
        if TRUE {
            CtSelect::ct_select(self.cond, self.then, else_)
        } else {
            CtSelect::ct_select(self.cond, else_, self.then)
        }
    }
}

impl BitAnd for CtBool {
    type Output = CtBool;
    #[inline]
    fn bitand(self, rhs: CtBool) -> CtBool {
        CtBool::protect_u8(self.to_u8() & rhs.to_u8())
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
        // raw_unchecked is fine here because the invariant
        // of ctbool is that the compiler can't tell if the k
        CtBool::from_raw_unchecked(self.to_u8() | rhs.to_u8())
    }
}

impl BitXor for CtBool {
    type Output = CtBool;
    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        CtBool::from_raw_unchecked(self.to_u8() ^ rhs.to_u8())
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
        // the optimizer can tell & 1 means the result is in {0,1}
        // so we need to protect
        CtBool::protect_u8(1u8 & (!self.to_u8()))
    }
}

pub trait CtEq {
    fn ct_eq(&self, other: &Self) -> CtBool;

    #[inline]
    fn ct_neq(&self, other: &Self) -> CtBool {
        !self.ct_eq(other)
    }
}

impl<const N: usize, T: CtEq> CtEq for [T; N] {
    #[inline]
    fn ct_eq(&self, rhs: &Self) -> CtBool {
        util::ct_all(self, rhs, CtEq::ct_eq)
    }
}

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
        self.ct_gt(other).if_true(self).else_(other)
    }

    #[inline]
    fn ct_min(&self, other: &Self) -> Self
    where
        Self: CtSelect,
    {
        self.ct_lt(other).if_true(self).else_(other)
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
        impl CtEq for $t_u {
            #[inline]
            fn ct_eq(&self, other: &$t_u) -> CtBool {
                // x == 0 if and only if self == other
                let x = self ^ other;

                // If x == 0, then x and -x are both equal to zero;
                // otherwise, one or both will have its high bit set.
                let y = (x | x.wrapping_neg()) >> (<$t_u>::BITS - 1);

                // Result is the opposite of the high bit (now shifted to low).
                CtBool::protect_u8((y ^ 1) as u8)
            }
        }

        impl CtEq for $t_i {
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
                let res = ((!b & a) | ((!(a ^ b)) & diff)) >> (<$t_u>::BITS - 1);
                CtBool::protect_u8(res as u8)
            }
        }

        impl CtOrd for $t_i {
            fn ct_gt(&self, other: &Self) -> CtBool {
                let sign_mask = 1 << (<$t_i>::BITS - 1);
                let a = (*self as $t_u) ^ sign_mask;
                let b = (*other as $t_u) ^ sign_mask;
                a.ct_gt(&b)
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
#[cfg(target_pointer_width = "64")]
impl CtSelect for usize {
    #[inline]
    fn ct_select(choice: CtBool, then: &Self, else_: &Self) -> Self {
        let then = *then as u64;
        let else_ = *else_ as u64;
        choice.if_true(&then).else_(&else_) as usize
    }
}

#[cfg(target_pointer_width = "32")]
impl CtSelect for usize {
    #[inline]
    fn ct_select(choice: CtBool, then: &Self, else_: &Self) -> Self {
        let then = *then as u32;
        let else_ = *else_ as u32;
        choice.if_true(&then).else_(&else_) as usize
    }
}

#[cfg(any(target_pointer_width = "64", target_pointer_width = "32"))]
impl CtSelect for isize {
    #[inline]
    fn ct_select(choice: CtBool, then: &Self, else_: &Self) -> Self {
        let then = *then as usize;
        let else_ = *else_ as usize;
        choice.if_true(&then).else_(&else_) as isize
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
        let res = choice.if_true(&then).else_(&else_);

        // # SAFETY: res is guaranteed to be in {-1, 0, 1} because it is either a or b which were
        // originally orderings
        unsafe { util::i8_to_ordering(res) }
    }
}

impl<T: CtSelect, const N: usize> CtSelect for [T; N] {
    #[inline]
    fn ct_select(choice: CtBool, then: &[T; N], else_: &[T; N]) -> Self {
        util::arr_combine(then, else_, |t_elem, e_elem| {
            choice.if_true(t_elem).else_(e_elem)
        })
    }
}

/// Unlike [T; N], &[T] does not implement [`CtEq`] and [`CtOrd`] because the two
/// slices being compared might be of different lengths which would leak information about whether
/// the two operands have identical types.
///
/// `&PublicLenSlice<T>` is effectively an alias for `&[T]` that allows users to explicitly opt-in
/// to this short-circuiting behavior. Note that the [`CtEq`] implementation for this type
/// still uses [`CtEq::ct_eq`] to compare the lengths. However, if they are not equal, the
/// implementation will return early.
#[repr(transparent)]
pub struct PublicLenSlice<T>(pub [T]);

impl<T> PublicLenSlice<T> {
    pub fn from_slice(slice: &[T]) -> &Self {
        // # SAFETY:
        // This is safe because #[repr(transparent)]
        let ptr = &raw const *slice as *const Self;

        unsafe { &*ptr }
    }

    pub fn from_mut_slice(slice: &mut [T]) -> &mut Self {
        // # SAFETY:
        // This is safe because #[repr(transparent)]
        let ptr = &raw mut *slice as *mut Self;

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

impl<T: CtEq> CtEq for PublicLenSlice<T> {
    #[inline]
    fn ct_eq(&self, rhs: &Self) -> CtBool {
        // The contract here is that the length is public so we could just do !=
        // the point is here i want people to have to explicitly opt in to potential leakage when
        // comparing slices, but we don't actually have to fully leak the length
        // this does leak if one is longer though
        if self.len().ct_neq(&rhs.len()).expose() {
            return CtBool::FALSE;
        }

        util::ct_all(self, rhs, CtEq::ct_eq)
    }
}

impl<T: CtOrd> CtOrd for PublicLenSlice<T> {
    #[inline]
    fn ct_gt(&self, other: &Self) -> CtBool {
        if self.len().ct_gt(&other.len()).expose() {
            CtBool::TRUE
        } else if self.len().ct_lt(&other.len()).expose() {
            CtBool::FALSE
        } else {
            util::ct_all(self, other, CtOrd::ct_gt)
        }
    }
}

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
