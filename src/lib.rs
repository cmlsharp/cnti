#![warn(clippy::pedantic)]
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

/// The `CtBool` struct represents a boolean that is used for "branching" in branchless,
/// constant-time programs
///
/// It aims to prevent LLVM from using its knowledge of the fact that a bool is either `0` or `1`
/// to re-insert branches in otherwise branchless code. Constructing a `CtBool` from
/// `CtBool::protect(my_boolean)` passes the boolean through an optimization barrier that is a
/// best-effort attempt to prevent such optimizations. This should be done as early as possible in
/// the computation. It is very similar to
/// [`subtle::Choice`](https://docs.rs/subtle/2.6.1/subtle/struct.Choice.html).
///
/// # Example usage:
///
/// ```no_run
/// use cnti::{CtBool, CtEq, CtSelectExt};
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
    /// A `CtBool` representing the boolean value `true`.
    // despite calling protect here black_box does not prevent the compiler from knowing these are
    // true and false respectively
    pub const TRUE: CtBool = CtBool::protect(true);

    /// A `CtBool` representing the boolean value `false`.
    pub const FALSE: CtBool = CtBool::protect(false);

    /// Creates a `CtBool` from a boolean value, passing it through an optimization barrier
    /// to prevent the compiler from knowing it is a boolean (restricted to 0 or 1), forcing
    /// it to treat the value as a general integer instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtBool;
    ///
    /// let ct_true = CtBool::protect(true);
    /// assert!(ct_true.expose());
    ///
    /// let ct_false = CtBool::protect(false);
    /// assert!(!ct_false.expose());
    /// ```
    #[inline]
    #[must_use]
    pub const fn protect(b: bool) -> Self {
        CtBool::protect_u8(b as u8)
    }

    /// Reveals the underlying boolean, removing any timing protections.
    /// This should generally be performed only once the value is safe to reveal
    #[inline]
    #[must_use]
    pub const fn expose(self) -> bool {
        self.to_u8() != 0
    }

    /// Yields the underlying u8 (which is guaranteed to be either 0 or 1, though the optimizer
    /// should be unaware of this fact)
    ///
    /// Library users should nonetheless be careful with how they use this value if they choose to
    /// expose it.
    #[inline]
    #[must_use]
    pub const fn to_u8(self) -> u8 {
        self.0.expose_const()
    }

    /// Perform a constant time selection via method chain syntax instead of calling
    /// [`CtSelect::ct_select`]. No computation is performed until [`CtIf::else_`] is called on the
    /// returned object.
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
    #[inline]
    #[must_use]
    pub fn if_true<'a, T: CtSelect>(&self, then: &'a T) -> CtIf<'a, T, true> {
        CtIf::<'_, _, true> { cond: *self, then }
    }

    /// Perform a constant time selection via method chain syntax instead of calling
    /// [`CtSelect::ct_select`]. No computation is performed until [`CtIf::else_`] is called on the
    /// returned object.
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
    #[inline]
    #[must_use]
    pub fn if_false<'a, T: CtSelect>(&self, then: &'a T) -> CtIf<'a, T, false> {
        CtIf::<'_, _, false> { cond: *self, then }
    }

    #[inline]
    // TODO: Decide whether we want to make this public
    // I'm kinda inclined to say no. If you have a u8, you can always
    // construct a CtBool via my_u8.ct_neq(&0).if_true(CtBool::TRUE).else_(CtBool::FALSE)
    // I want a privat einner function for cases where I _know_ the u8 is 1 or 0 (but i want to
    // hide this from the optimizer).
    #[must_use]
    const fn protect_u8(inner: u8) -> Self {
        debug_assert!(inner == 0 || inner == 1);
        Self(BlackBox::protect(inner))
    }

    // this function should only ever be called when the optimizer should be unable to tell that
    // the u8 must be either 0 or 1
    #[must_use]
    const fn from_u8_no_protect(inner: u8) -> Self {
        debug_assert!(inner == 0 || inner == 1);
        Self(BlackBox::from_raw_unchecked(inner))
    }
}

/// Represents an incomplete [`CtSelect`] expression.
/// See the documentation for [`CtBool::if_true`]/[`CtBool::if_false`].
pub struct CtIf<'a, T, const IS_TRUE: bool> {
    cond: CtBool,
    then: &'a T,
}

impl<T, const IS_TRUE: bool> CtIf<'_, T, IS_TRUE> {
    /// Perform the `ct_select` by providing the alternative value
    #[must_use]
    pub fn else_(self, else_: &T) -> T
    where
        T: CtSelect,
    {
        // this is a compile-time condition, not a runtime branch!
        if IS_TRUE {
            CtSelect::ct_select(self.cond, self.then, else_)
        } else {
            CtSelect::ct_select(self.cond, else_, self.then)
        }
    }
}

impl BitAnd for CtBool {
    type Output = CtBool;
    // TODO determine if no protect is sound on binary ops
    // Can bad stuff happen if you include CtBool::TRUE in your binary expression chain?
    // I can't seem to make it happen, but more investigation is required
    #[inline]
    fn bitand(self, rhs: CtBool) -> CtBool {
        CtBool::from_u8_no_protect(self.to_u8() & rhs.to_u8())
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
        // no_protect is fine here because the invariant
        // of ctbool is that the compiler can't tell if the k
        CtBool::from_u8_no_protect(self.to_u8() | rhs.to_u8())
    }
}

impl BitXor for CtBool {
    type Output = CtBool;
    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        CtBool::from_u8_no_protect(self.to_u8() ^ rhs.to_u8())
    }
}

impl BitXorAssign for CtBool {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
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

/// Constant-time equality comparison.
///
/// This trait provides methods for comparing values for equality in constant time,
/// returning a [`CtBool`] instead of a regular `bool`. The primary use case is in
/// conjunction with [`CtSelect`] for constant-time conditional operations.
///
/// # Examples
///
/// ```
/// use cnti::CtEq;
///
/// let a = 42u32;
/// let b = 42u32;
/// let c = 100u32;
///
/// assert!(a.ct_eq(&b).expose());
/// assert!(!a.ct_eq(&c).expose());
/// assert!(a.ct_neq(&c).expose());
/// ```
pub trait CtEq {
    /// Returns a `CtBool` indicating whether `self` equals `other` in constant time.
    #[must_use]
    fn ct_eq(&self, other: &Self) -> CtBool;

    /// Returns a `CtBool` indicating whether `self` does not equal `other` in constant time.
    ///
    /// This is the logical negation of `ct_eq`.
    #[inline]
    #[must_use]
    fn ct_neq(&self, other: &Self) -> CtBool {
        !self.ct_eq(other)
    }
}

impl<const N: usize, T: CtEq> CtEq for [T; N] {
    #[inline]
    fn ct_eq(&self, rhs: &Self) -> CtBool {
        util::ct_zip_all(self, rhs, CtEq::ct_eq)
    }
}

impl<const N: usize, T: CtOrd> CtOrd for [T; N] {
    #[inline]
    fn ct_gt(&self, other: &Self) -> CtBool {
        util::ct_lexicographic_gt(self, other)
    }
}

/// Constant-time ordering comparison.
///
/// This trait provides methods for comparing values for ordering in constant time,
/// returning a [`CtBool`] instead of a regular `bool`. The primary use case is in
/// conjunction with [`CtSelect`] for constant-time conditional operations.
///
/// # Examples
///
/// ```
/// use cnti::CtOrd;
///
/// let a = 10u32;
/// let b = 20u32;
///
/// assert!(a.ct_lt(&b).expose());
/// assert!(b.ct_gt(&a).expose());
/// assert!(a.ct_leq(&b).expose());
/// assert!(b.ct_geq(&a).expose());
/// ```
pub trait CtOrd: CtEq {
    /// Returns a `CtBool` indicating whether `self` is greater than `other` in constant time.
    #[must_use]
    fn ct_gt(&self, other: &Self) -> CtBool;

    /// Returns a `CtBool` indicating whether `self` is less than or equal to `other` in constant time.
    ///
    /// This is the logical negation of `ct_gt`.
    #[inline]
    #[must_use]
    fn ct_leq(&self, other: &Self) -> CtBool {
        !self.ct_gt(other)
    }

    /// Returns a `CtBool` indicating whether `self` is less than `other` in constant time.
    #[inline]
    #[must_use]
    fn ct_lt(&self, other: &Self) -> CtBool {
        other.ct_gt(self)
    }

    /// Returns a `CtBool` indicating whether `self` is greater than or equal to `other` in constant time.
    ///
    /// This is the logical negation of `ct_lt`.
    #[inline]
    #[must_use]
    fn ct_geq(&self, other: &Self) -> CtBool {
        !self.ct_lt(other)
    }

    /// Returns the maximum of `self` and `other` in constant time.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOrd;
    ///
    /// assert_eq!(5u32.ct_max(&10), 10);
    /// assert_eq!(10u32.ct_max(&5), 10);
    /// ```
    #[inline]
    #[must_use]
    fn ct_max(&self, other: &Self) -> Self
    where
        Self: CtSelect,
    {
        self.ct_gt(other).if_true(self).else_(other)
    }

    /// Returns the minimum of `self` and `other` in constant time.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOrd;
    ///
    /// assert_eq!(5u32.ct_min(&10), 5);
    /// assert_eq!(10u32.ct_min(&5), 5);
    /// ```
    #[inline]
    #[must_use]
    fn ct_min(&self, other: &Self) -> Self
    where
        Self: CtSelect,
    {
        self.ct_gt(other).if_false(self).else_(other)
    }

    /// Restricts `self` to a certain interval in constant time.
    ///
    /// Returns `max` if `self` is greater than `max`, `min` if `self` is less than `min`,
    /// and `self` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOrd;
    ///
    /// assert_eq!(5u32.ct_clamp(&10, &20), 10);
    /// assert_eq!(15u32.ct_clamp(&10, &20), 15);
    /// assert_eq!(25u32.ct_clamp(&10, &20), 20);
    /// ```
    #[inline]
    #[must_use]
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
            // I actually don't know if this is any better than
            // CtBool::protect(*self == *other).
            // The compiler can tell this is equality, it outputs a cmp instruction on x86
            // But our other measures still prevent it from outputting branches
            #[allow(clippy::cast_possible_truncation)]
            fn ct_eq(&self, other: &$t_u) -> CtBool {
                // x == 0 if and only if self == other
                let x = self ^ other;

                // If x == 0, then x and -x are both equal to zero;
                // otherwise, one or both will have its high bit set. respectively
                let y = (x | x.wrapping_neg()) >> (<$t_u>::BITS - 1);

                // Result is the opposite of the high bit (now shifted to low).
                CtBool::protect_u8((y ^ 1) as u8)
            }
        }

        impl CtEq for $t_i {
            #[inline]
            fn ct_eq(&self, other: &$t_i) -> CtBool {
                // Bitcast to unsigned and call that implementation.
                (*self).cast_unsigned().ct_eq(&(*other).cast_unsigned())
            }
        }

        impl CtOrd for $t_u {
            #[allow(clippy::cast_possible_truncation)]
            fn ct_gt(&self, other: &$t_u) -> CtBool {
                let a = *self;
                let b = *other;
                let diff = b.wrapping_sub(a);
                let res = ((!b & a) | ((!(a ^ b)) & diff)) >> (<$t_u>::BITS - 1);
                CtBool::protect_u8(res as u8)
            }
        }

        impl CtOrd for $t_i {
            #[allow(clippy::cast_possible_truncation)]
            fn ct_gt(&self, other: &Self) -> CtBool {
                let sign_mask = 1 << (<$t_i>::BITS - 1);
                let a = self.cast_unsigned() ^ sign_mask;
                let b = other.cast_unsigned() ^ sign_mask;
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
                let then = then.cast_unsigned();
                let else_ = else_.cast_unsigned();
                CtSelect::ct_select(choice, &then, &else_).cast_signed()
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

// these annoyingly don't have implementations in the cmov crate, pending that we just cast them to
// the right width type depending on target_pointer_width. I guess I don't have a case for 16-bit
// platforms. lol
#[cfg(target_pointer_width = "64")]
impl CtSelect for usize {
    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    fn ct_select(choice: CtBool, then: &Self, else_: &Self) -> Self {
        let then = *then as u64;
        let else_ = *else_ as u64;
        choice.if_true(&then).else_(&else_) as usize
    }
}

#[cfg(target_pointer_width = "32")]
impl CtSelect for usize {
    #[inline]
    #[allow(clippy::cast_possible_truncation)]
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
        let then = then.cast_unsigned();
        let else_ = else_.cast_unsigned();
        choice.if_true(&then).else_(&else_).cast_signed()
    }
}

/// Constant time selection based on a [`CtBool`].
///
/// Implementors of this trait additionally get a blanket implementation for [`CtSelectExt`] which
/// provides conditional assignment, swapping, etc.
///
/// # Examples
///
/// ```
/// use cnti::{CtSelect, CtBool};
///
/// let result = u32::ct_select(CtBool::TRUE, &42, &100);
/// assert_eq!(result, 42);
///
/// let result = u32::ct_select(CtBool::FALSE, &42, &100);
/// assert_eq!(result, 100);
/// ```
// TODO: Figure out if it makes sense for this to take by value!
// This would allow for efficient implementations of e.g. CtSelect for
// larger data structures that wouldn't implicitly require cloning
// But I don't know how to generically write e.g. swap_if or replace_if in terms of ct_select in that
// case, they couldn't have default impls any more which would suck
// The interface would have to change, something like returning both the taken and not taken value
// However, it would be very easy to accidentally implement such an interface in such a way that
// would leak info thru memory access pattern
pub trait CtSelect: Sized {
    /// Selects `then` if `choice` is true, otherwise selects `else_`, in constant time.
    ///
    /// This operation always executes in constant time regardless of the value of `choice`.
    #[must_use]
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
    #[must_use]
    fn ct_replace_if(&mut self, other: &Self, choice: CtBool) -> Self {
        core::mem::replace(self, Self::ct_select(choice, other, self))
    }

    /// Conditionally swaps `other` with `self`
    /// In other words, `x.ct_swap_if(&mut y, choice)` is the constant-time equivalent of
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
    /// ```
    #[inline]
    fn ct_swap_if(&mut self, other: &mut Self, choice: CtBool) {
        let old_self = self.ct_replace_if(other, choice);
        let _ = other.ct_replace_if(&old_self, choice);
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
    /// ```
    #[inline]
    #[must_use]
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

/// Unlike `[T; N]` (which already implements [`CtEq`] and [`CtOrd`]), `[T]` does not implement
/// these traits because the length is not known at compile time, and as such the time for these
/// operations are inherently not data-independent.
///
/// However, in many cases, the length of a slice is not in fact secret (even if it isn't known at
/// compile time), and for such cases, one can explicitly construct a `&PublicLenSlice<T>` from a
/// `&[T]` (via [`PublicLenSlice::from_slice`]) which asserts that operations which leak the
/// lengths of the given slices through timing are acceptable.
///
/// Note that aside from having implementations for `CtEq` and `CtOrd`, this type behaves exactly
/// like `[T]`. References to it decay to `&[T]`. This means that e.g. `==` uses `[T]::eq`. It is
/// not a 'constant time slice', it is a slice where the programmer explicitly opts in to length
/// short-circuiting meaning that it can implement `CtEq` and `CtOrd`.
#[repr(transparent)]
pub struct PublicLenSlice<T>(pub [T]);

impl<T> PublicLenSlice<T> {
    /// Creates a `&PublicLenSlice<T>` from a `&[T]`.
    ///
    /// This explicitly marks that operations which leak the length of the slice through
    /// timing are acceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::{PublicLenSlice, CtEq};
    ///
    /// let data = vec![1u32, 2, 3];
    /// let slice: &[u32] = &data[..];
    /// let public_len_slice = PublicLenSlice::from_slice(slice);
    ///
    /// let other = vec![1u32, 2, 3];
    /// let other_slice: &[u32] = &other[..];
    /// let other_public_len = PublicLenSlice::from_slice(other_slice);
    ///
    /// assert!(public_len_slice.ct_eq(other_public_len).expose());
    /// ```
    #[must_use]
    pub fn from_slice(slice: &[T]) -> &Self {
        // # SAFETY:
        // This is safe because #[repr(transparent)]
        let ptr = &raw const *slice as *const Self;

        unsafe { &*ptr }
    }

    /// Creates a `&mut PublicLenSlice<T>` from a `&mut [T]`.
    ///
    /// This explicitly marks that operations which leak the length of the slice through
    /// timing are acceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::{PublicLenSlice, CtOrd, CtSelectExt, CtBool};
    ///
    /// let mut data = vec![1u32, 2, 3];
    /// let slice: &mut [u32] = &mut data[..];
    /// let public_len_slice = PublicLenSlice::from_mut_slice(slice);
    ///
    /// // Perform conditional assignment
    /// public_len_slice[0].ct_replace_if(&42, CtBool::TRUE);
    /// assert_eq!(public_len_slice[0], 42);
    ///
    /// // Can now use CtOrd operations on the slice
    /// let other = vec![1u32, 2, 3];
    /// let other_slice: &[u32] = &other[..];
    /// let other_public_len = PublicLenSlice::from_slice(other_slice);
    /// assert!(public_len_slice.ct_gt(other_public_len).expose());
    /// ```
    #[must_use]
    pub fn from_mut_slice(slice: &mut [T]) -> &mut Self {
        // # SAFETY:
        // This is safe because #[repr(transparent)]
        let ptr = &raw mut *slice as *mut Self;

        unsafe { &mut *ptr }
    }
}

impl<T> core::fmt::Debug for &PublicLenSlice<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "PublicLenSlice([_; {}])", self.len())
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

impl<T, U> core::borrow::Borrow<T> for PublicLenSlice<U>
where
    T: ?Sized,
    <PublicLenSlice<U> as Deref>::Target: core::borrow::Borrow<T>,
{
    fn borrow(&self) -> &T {
        self.deref().borrow()
    }
}

impl<T, U> core::borrow::BorrowMut<T> for PublicLenSlice<U>
where
    T: ?Sized,
    <PublicLenSlice<U> as Deref>::Target: core::borrow::BorrowMut<T>,
{
    fn borrow_mut(&mut self) -> &mut T {
        self.deref_mut().borrow_mut()
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
        if self.len() != rhs.len() {
            return CtBool::FALSE;
        }

        util::ct_zip_all(self, rhs, CtEq::ct_eq)
    }
}

impl<T: CtOrd> CtOrd for PublicLenSlice<T> {
    #[inline]
    fn ct_gt(&self, other: &Self) -> CtBool {
        if self.len() != other.len() {
            return CtBool::protect(self.len() > other.len());
        }
        util::ct_lexicographic_gt(self, other)
    }
}

mod util {
    use super::{CtBool, CtOrd};
    // this will leak min(lhs.len(), rhs.len())!
    #[must_use]
    pub(crate) fn ct_zip_all<T>(lhs: &[T], rhs: &[T], f: impl Fn(&T, &T) -> CtBool) -> CtBool {
        lhs.iter()
            .zip(rhs)
            .fold(CtBool::TRUE, |acc, (l, r)| acc & f(l, r))
    }

    // this will leak min(lhs.len(), rhs.len())
    #[allow(unused)]
    #[must_use]
    pub(crate) fn ct_zip_any<T>(lhs: &[T], rhs: &[T], f: impl Fn(&T, &T) -> CtBool) -> CtBool {
        lhs.iter()
            .zip(rhs)
            .fold(CtBool::FALSE, |acc, (l, r)| acc | f(l, r))
    }

    // Lexicographic comparison: returns true if lhs > rhs in constant time
    // Iterates through all elements to avoid timing leaks
    #[must_use]
    pub(crate) fn ct_lexicographic_gt<T: CtOrd>(lhs: &[T], rhs: &[T]) -> CtBool {
        let mut result = CtBool::FALSE;
        let mut found_diff = CtBool::FALSE;

        for (l, r) in lhs.iter().zip(rhs) {
            let is_gt = l.ct_gt(r);
            let is_eq = l.ct_eq(r);

            // Update result only if we haven't found a difference yet
            result = found_diff.if_true(&result).else_(&is_gt);

            // Mark that we found a difference if elements are not equal
            found_diff |= !is_eq;
        }

        result
    }

    // Takes two arrays of size n and produces a new array of size n whose ith element is f(lhs[i],
    // rhs[i])
    #[must_use]
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
    #[must_use]
    pub(crate) unsafe fn i8_to_ordering(x: i8) -> core::cmp::Ordering {
        debug_assert!(x == -1 || x == 0 || x == 1);

        let res_ptr = (&raw const x).cast();
        // # SAFETY: this is safe because core::cmp::Ordering is repr(i8) with all variants in the
        // range {-1, 0, 1}. Per the safety contract of this function, x in {-1, 0, 1}
        unsafe { *res_ptr }
    }
}
