#![no_std]

use cmov::Cmov;
use core::hint;

pub use cnti_derive::{CtEq, CtOrd, CtPartialEq, CtSelect};

use core::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Deref, DerefMut, Not,
};

#[repr(transparent)]
// is deriving this fine, or should i manually impl so pulling stuff out of blackbox goes through
// expose?
#[derive(Clone, Copy, Default, CtEq, CtPartialEq, CtOrd, CtSelect)]
/// Puts T behind a core::hint::black_box optimization barrier.
/// Note that this is just a best effort attempt to prevent LLVM from making
/// non-constant-time optimizations wrt T. The compiler is technically free to ignore this.
/// Assembly should always be manually verified.
pub struct BlackBox<T>(T);

impl<T> core::fmt::Debug for BlackBox<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "BlackBox")
    }
}

impl<T> BlackBox<T> {
    pub const fn protect(b: T) -> Self {
        Self(hint::black_box(b))
    }

    // XXX once Destruct trait is stable, we can make this a const function probably
    pub fn expose(self) -> T {
        hint::black_box(self.0)
    }

    // TODO: deprecate once Destruct trait is stable
    pub const fn expose_const(self) -> T
    where
        T: Copy,
    {
        hint::black_box(self.0)
    }
}

#[derive(Copy, Clone, Default, CtEq, CtOrd, CtSelect)]
#[repr(transparent)]
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
pub struct CtBool(BlackBox<u8>);

impl core::fmt::Debug for CtBool {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "CtBool")
    }
}

impl CtPartialEq for CtBool {
    #[inline]
    fn ct_eq(&self, rhs: &CtBool) -> CtBool {
        !(*self ^ *rhs)
    }
}

impl CtBool {
    pub const TRUE: CtBool = CtBool::protect(true);
    pub const FALSE: CtBool = CtBool::protect(false);

    #[inline]
    pub const fn protect(b: bool) -> Self {
        CtBool::from_u8(b as u8)
    }

    #[inline]
    pub const fn expose(self) -> bool {
        self.to_u8() != 0
    }

    #[inline]
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
    fn ct_gt(&self, other: &Self) -> CtBool {
        util::ct_all(self, other, CtOrd::ct_gt)
    }

    fn ct_lt(&self, other: &Self) -> CtBool {
        util::ct_all(self, other, CtOrd::ct_lt)
    }

    fn ct_leq(&self, other: &Self) -> CtBool {
        util::ct_all(self, other, CtOrd::ct_leq)
    }

    fn ct_geq(&self, other: &Self) -> CtBool {
        util::ct_all(self, other, CtOrd::ct_geq)
    }
}

pub trait CtOrd: CtEq {
    fn ct_gt(&self, other: &Self) -> CtBool;

    fn ct_leq(&self, other: &Self) -> CtBool {
        !self.ct_gt(other)
    }

    fn ct_lt(&self, other: &Self) -> CtBool {
        other.ct_gt(self)
    }

    fn ct_geq(&self, other: &Self) -> CtBool {
        !self.ct_lt(other)
    }

    fn ct_max(&self, other: &Self) -> Self
    where
        Self: CtSelect,
    {
        Self::ct_select(self.ct_gt(other), self, other)
    }

    fn ct_min(&self, other: &Self) -> Self
    where
        Self: CtSelect,
    {
        Self::ct_select(self.ct_gt(other), self, other)
    }

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
                CtBool::from_u8(((y ^ (1 as $t_u)) as u8))
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
            #[inline]
            fn ct_gt(&self, other: &$t_u) -> CtBool {
                let gtb = self & !other; // All the bits in self that are greater than their corresponding bits in other.
                let mut ltb = !self & other; // All the bits in self that are less than their corresponding bits in other.
                let mut pow = 1;

                // Less-than operator is okay here because it's dependent on the bit-width.
                while pow < <$t_u>::BITS {
                    ltb |= ltb >> pow; // Bit-smear the highest set bit to the right.
                    pow += pow;
                }
                let mut bit = gtb & !ltb; // Select the highest set bit.
                let mut pow = 1;

                while pow < <$t_u>::BITS {
                    bit |= bit >> pow; // Shift it to the right until we end up with either 0 or 1.
                    pow += pow;
                }
                // XXX We should possibly do the above flattening to 0 or 1 in the
                //     Choice constructor rather than making it a debug error?
                CtBool::from_u8((bit & 1) as u8)
            }
        }

        impl CtEq for $t_i {}

        impl CtOrd for $t_i {
            fn ct_gt(&self, other: &Self) -> CtBool {
                let unsigned_self = *self as $t_u;
                let unsigned_other = *other as $t_u;
                let abs_self = unsigned_self & ((<$t_u>::MAX - 1) >> 1);
                let abs_other = unsigned_other & ((<$t_u>::MAX - 1) >> 1);

                let self_is_neg =
                    CtBool::from_u8(((unsigned_self >> (<$t_u>::BITS - 1)) & 1) as u8);
                let other_is_neg =
                    CtBool::from_u8(((unsigned_other >> (<$t_u>::BITS - 1)) & 1) as u8);

                let sign_diff = self_is_neg ^ other_is_neg;

                (!self_is_neg & other_is_neg) | (abs_self.ct_gt(&abs_other) & !sign_diff)
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
        util::arr_zip(then, else_, |t_elem, e_elem| {
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

impl<T> core::fmt::Debug for &PublicLenSlice<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "PublicLenSlice")
    }
}

impl<'a, T> From<&'a [T]> for &'a PublicLenSlice<T> {
    fn from(value: &'a [T]) -> Self {
        // # SAFETY:
        // This is safe because #[repr(transparent)]
        let ptr = value as *const [T] as *const PublicLenSlice<T>;

        unsafe { &*ptr }
    }
}

impl<'a, T> From<&'a mut [T]> for &'a mut PublicLenSlice<T> {
    fn from(value: &'a mut [T]) -> Self {
        // # SAFETY:
        // This is safe because #[repr(transparent)]
        let ptr = value as *mut [T] as *mut PublicLenSlice<T>;
        unsafe { &mut *ptr }
    }
}

impl<T> Deref for PublicLenSlice<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for PublicLenSlice<T> {
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

/// The `CtOption<T>` type represents an optional value similar to the
/// [`Option<T>`](core::option::Option) type but is intended for
/// use in constant time APIs.
///
/// Any given `CtOption<T>` is either `Some` or `None`, but unlike
/// `Option<T>` these variants are not exposed. The
/// [`is_some()`](CtOption::is_some) method is used to determine if
/// the value is `Some`, and [`unwrap_or()`](CtOption::unwrap_or) methods are
/// provided to access the underlying value. The value can also be
/// obtained with [`unwrap()`](CtOption::unwrap) but this will panic
/// if it is `None`.
///
///
/// Functions that are intended to be constant time may not produce
/// valid results for all inputs, such as square root and inversion
/// operations in finite field arithmetic. Returning an `Option<T>`
/// from these functions makes it difficult for the caller to reason
/// about the result in constant time, and returning an incorrect
/// value burdens the caller and increases the chance of bugs.
///
/// Generally `CtOption<T>` supports most of the methods that are
/// supported for [`Option<T>`](core::option::Option), with the exception
/// of some methods that really only make sense in a non-constant time constext.
/// (For example, while [`unwrap_or()`](CtOption::unwrap_or) is supported, there is no
/// equivalent of [`Option::unwrap_or_else`](core::option::Option::unwrap_or_else) since the
/// provided closure would need to be called regardless of whether the `CtOption` is conceptually
/// `Some` or `None`, and hence this is identical to `ct_opt.unwrap_or(f())`.
#[derive(Clone, Copy, Default, CtSelect, CtEq)]
pub struct CtOption<T> {
    value: T,
    is_some: CtBool,
}

impl<T> core::fmt::Debug for CtOption<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "CtOption")
    }
}

impl<T: CtPartialEq> CtPartialEq for CtOption<T> {
    fn ct_eq(&self, other: &Self) -> CtBool {
        (self.is_none() & other.is_none()) | (self.value.ct_eq(&other.value))
    }
}

impl<T> CtOption<T> {
    /// This method is used to construct a new `CtOption<T>` and takes
    /// a value of type `T`, and a `Choice` that determines whether
    /// the optional value should be `Some` or not. If `is_some` is
    /// false, the value will still be stored but its value is never
    /// exposed (except through `_unchecked` methods).
    pub const fn new(value: T, is_some: CtBool) -> Self {
        Self { value, is_some }
    }

    /// Convert the `CtOption<T>` wrapper into an `Option<T>`, depending on whether
    /// the underlying `is_some` `CtBool`.
    ///
    /// # Note
    ///
    /// This implementation doesn't intend to be constant-time nor try to protect the
    /// leakage of the `T` since the `Option<T>` will do it anyways.
    pub fn expose(self) -> Option<T> {
        if self.is_some.expose() {
            Some(self.value)
        } else {
            None
        }
    }

    /// Returns the contained value of type `T`, regardless of `is_some`.
    ///
    /// This is the equivalent of
    /// [`Option::unwrap_unchecked`](core::option::Option::unwrap_unchecked), except that it is not
    /// `unsafe` since there is always an inner value of type `T`.
    pub fn unwrap_unchecked(self) -> T {
        self.value
    }

    /// Returns a true `CtBool` if this value is `Some`.
    pub const fn is_some(&self) -> CtBool {
        self.is_some
    }

    /// Returns a true `CtBool` if this value is `None`.
    pub fn is_none(&self) -> CtBool {
        !self.is_some
    }

    /// Converts an `&CtOption<T>` to a `CtOption<&T>.
    pub const fn as_ref(&self) -> CtOption<&T> {
        CtOption {
            value: &self.value,
            is_some: self.is_some,
        }
    }

    /// Converts an `&mut CtOption<T>` to a `CtOption<&mut T>.
    pub const fn as_mut(&mut self) -> CtOption<&mut T> {
        CtOption {
            value: &mut self.value,
            is_some: self.is_some,
        }
    }

    /// Returns the contained `Some` value or a provided default.
    pub fn unwrap_or(self, def: T) -> T
    where
        T: CtSelect,
    {
        T::ct_select(self.is_some, &self.value, &def)
    }

    /// Returns the contained `Some` value or a default.
    pub fn unwrap_or_default(self) -> T
    where
        T: CtSelect + Default,
    {
        self.unwrap_or(T::default())
    }

    /// Maps a `CtOption<T>` to a `CtOption<U>` by applying the provided closure.
    ///
    /// Note that the provided closure will be executed regardless of whether the inner value is
    /// `Some` or `None`. If the inner value is `None`, the closure will be executed on
    /// `T::Default()`
    pub fn map<U, F>(self, f: F) -> CtOption<U>
    where
        F: FnOnce(T) -> U,
        T: Default + CtSelect,
    {
        CtOption {
            is_some: self.is_some,
            value: f(self.unwrap_or_default()),
        }
    }

    /// Maps a `CtOption<T>` to a `CtOption<U>` by applying the provided closure.
    ///
    /// Note that the provided closure will be executed regardless of whether the inner value is
    /// `Some` or `None`. The primary difference between this and `CtOption::map` is that when this
    /// `CtOption` is `None`, the closure will be called on whatever value it happens to contain.
    /// This is not `unsafe` as this is guaranteed to be a well-formed value of type `T`.
    pub fn map_unchecked<U, F>(self, f: F) -> CtOption<U>
    where
        F: FnOnce(T) -> U,
    {
        CtOption {
            value: f(self.value),
            is_some: self.is_some,
        }
    }

    pub fn map_or<U, F>(self, default: U, f: F) -> U
    where
        U: CtSelect,
        F: FnOnce(T) -> U,
        T: Default + CtSelect,
    {
        self.map(f).unwrap_or(default)
    }

    pub fn map_or_unchecked<U, F>(self, default: U, f: F) -> U
    where
        U: CtSelect,
        F: FnOnce(T) -> U,
    {
        self.map_unchecked(f).unwrap_or(default)
    }

    pub fn map_or_default<U, F>(self, f: F) -> U
    where
        U: CtSelect + Default,
        F: FnOnce(T) -> U,
        T: CtSelect + Default,
    {
        self.map(f).unwrap_or_default()
    }

    pub fn map_or_default_unchecked<U, F>(self, f: F) -> U
    where
        U: CtSelect + Default,
        F: FnOnce(T) -> U,
    {
        self.map_unchecked(f).unwrap_or_default()
    }

    pub fn as_deref(&self) -> CtOption<&<T as Deref>::Target>
    where
        T: Deref + CtSelect,
    {
        self.as_ref().map_unchecked(Deref::deref)
    }

    pub fn as_deref_mut(&mut self) -> CtOption<&mut <T as Deref>::Target>
    where
        T: DerefMut + CtSelect,
    {
        self.as_mut().map_unchecked(DerefMut::deref_mut)
    }

    pub fn and<U>(self, optb: CtOption<U>) -> CtOption<U> {
        CtOption {
            value: optb.value,
            is_some: self.is_some & optb.is_some,
        }
    }

    pub fn and_then<U, F>(self, f: F) -> CtOption<U>
    where
        F: FnOnce(T) -> CtOption<U>,
        T: CtSelect + Default,
    {
        self.map(f).flatten()
    }

    pub fn and_then_unchecked<U, F>(self, f: F) -> CtOption<U>
    where
        F: FnOnce(T) -> CtOption<U>,
    {
        self.map_unchecked(f).flatten()
    }

    pub fn or(self, optb: CtOption<T>) -> CtOption<T>
    where
        T: CtSelect,
    {
        CtOption {
            is_some: self.is_some | optb.is_some,
            value: self.unwrap_or(optb.value),
        }
    }

    pub fn insert(&mut self, value: T) -> &mut T {
        self.value = value;
        &mut self.value
    }

    pub fn get_or_insert(&mut self, value: T) -> &mut T
    where
        T: CtSelect,
    {
        self.value.ct_replace_if(&value, !self.is_some);
        &mut self.value
    }

    pub fn get_or_insert_default(&mut self) -> &mut T
    where
        T: CtSelect + Default,
    {
        self.value.ct_take_if(!self.is_some());
        &mut self.value
    }

    pub fn take(&mut self) -> CtOption<T>
    where
        T: Default,
    {
        core::mem::take(self)
    }

    pub fn replace(&mut self, value: T) -> CtOption<T> {
        core::mem::replace(
            self,
            CtOption {
                is_some: CtBool::TRUE,
                value,
            },
        )
    }

    pub fn zip<U>(self, other: CtOption<U>) -> CtOption<(T, U)> {
        CtOption {
            is_some: self.is_some & other.is_some,
            value: (self.value, other.value),
        }
    }
}

impl<T, U> CtOption<(T, U)> {
    pub fn unzip(self) -> (CtOption<T>, CtOption<U>) {
        let (t, u) = self.value;
        (
            CtOption {
                value: t,
                is_some: self.is_some,
            },
            CtOption {
                value: u,
                is_some: self.is_some,
            },
        )
    }
}

impl<T> CtOption<&T> {
    pub const fn copied(self) -> CtOption<T>
    where
        T: Copy,
    {
        CtOption {
            is_some: self.is_some,
            value: *self.value,
        }
    }

    /// Note that this is only constant time iff T::clone is
    pub fn cloned(self) -> CtOption<T>
    where
        T: Clone,
    {
        CtOption {
            is_some: self.is_some,
            value: self.value.clone(),
        }
    }
}

impl<T> CtOption<&mut T> {
    pub const fn copied(self) -> CtOption<T>
    where
        T: Copy,
    {
        CtOption {
            is_some: self.is_some,
            value: *self.value,
        }
    }

    pub fn cloned(self) -> CtOption<T>
    where
        T: Clone,
    {
        CtOption {
            is_some: self.is_some,
            value: self.value.clone(),
        }
    }
}

impl<T> CtOption<CtOption<T>> {
    pub fn flatten(self) -> CtOption<T> {
        let CtOption {
            is_some: outer,
            value: CtOption {
                is_some: inner,
                value,
            },
        } = self;

        CtOption {
            is_some: outer & inner,
            value,
        }
    }
}

impl<'a, T> From<&'a CtOption<T>> for CtOption<&'a T> {
    fn from(value: &'a CtOption<T>) -> Self {
        value.as_ref()
    }
}

impl<'a, T> From<&'a mut CtOption<T>> for CtOption<&'a mut T> {
    fn from(value: &'a mut CtOption<T>) -> Self {
        value.as_mut()
    }
}

impl<T> From<T> for CtOption<T> {
    fn from(value: T) -> Self {
        CtOption {
            value,
            is_some: CtBool::TRUE,
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
    pub(crate) fn arr_zip<T, const N: usize, U>(
        lhs: &[T; N],
        rhs: &[T; N],
        f: impl Fn(&T, &T) -> U,
    ) -> [U; N] {
        core::array::from_fn(|i| {
            // # SAFETY: core::array::from_fn guarantees that i will be in the range [0, N) and lhs and
            // rhs are both of array length N
            // Hence we use get_unchecked to remove the unnecessary bounds checking
            let l = unsafe { lhs.get_unchecked(i) };
            let r = unsafe { rhs.get_unchecked(i) };
            f(l, r)
        })
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
