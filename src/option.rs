#![allow(clippy::needless_pass_by_value)]
use crate::{CtBool, CtSelect, CtSelectExt};
use core::ops::{Deref, DerefMut};

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
#[derive(Clone, Copy, Default, CtSelect)]
pub struct CtOption<T> {
    value: T,
    is_some: CtBool,
}

impl<T> core::fmt::Debug for CtOption<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "CtOption")
    }
}

impl<T> CtOption<T> {
    /// This method is used to construct a new `CtOption<T>` and takes
    /// a value of type `T`, and a `CtBool` that determines whether
    /// the optional value should be `Some` or not. If `is_some` is
    /// false, the value will still be stored but its value is never
    /// exposed (except through `_unchecked` methods).
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::{CtOption, CtBool};
    ///
    /// let some_value = CtOption::new(42, CtBool::TRUE);
    /// assert!(some_value.is_some().expose());
    ///
    /// let none_value = CtOption::new(42, CtBool::FALSE);
    /// assert!(none_value.is_none().expose());
    /// ```
    pub const fn new(value: T, is_some: CtBool) -> Self {
        Self { value, is_some }
    }

    /// Equivalent to `CtOption::new(value, CtBool::TRUE)`
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let value = CtOption::some(42);
    /// assert!(value.is_some().expose());
    /// assert_eq!(value.expose(), Some(42));
    /// ```
    pub const fn some(value: T) -> Self {
        Self::new(value, CtBool::TRUE)
    }

    /// Equivalent to `CtOption::new(value, CtBool::FALSE)`
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let value = CtOption::none(42);
    /// assert!(value.is_none().expose());
    /// assert_eq!(value.expose(), None);
    /// ```
    pub const fn none(value: T) -> Self {
        Self::new(value, CtBool::FALSE)
    }

    /// Convert the `CtOption<T>` wrapper into an `Option<T>`, depending on whether
    /// the underlying `is_some` `CtBool`.
    ///
    /// # Note
    ///
    /// This implementation doesn't intend to be constant-time nor try to protect the
    /// leakage of the `T` since the `Option<T>` will do it anyways.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let some_value = CtOption::some(42);
    /// assert_eq!(some_value.expose(), Some(42));
    ///
    /// let none_value: CtOption<i32> = CtOption::none(0);
    /// assert_eq!(none_value.expose(), None);
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let some_value = CtOption::some(42);
    /// assert_eq!(some_value.unwrap_unchecked(), 42);
    ///
    /// // Even for None, this returns the inner value
    /// let none_value = CtOption::none(99);
    /// assert_eq!(none_value.unwrap_unchecked(), 99);
    /// ```
    pub fn unwrap_unchecked(self) -> T {
        self.value
    }

    /// Returns a true `CtBool` if this value is `Some`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let some_value = CtOption::some(42);
    /// assert!(some_value.is_some().expose());
    ///
    /// let none_value: CtOption<i32> = CtOption::none(0);
    /// assert!(!none_value.is_some().expose());
    /// ```
    pub const fn is_some(&self) -> CtBool {
        self.is_some
    }

    /// Returns a true `CtBool` if this value is `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let some_value = CtOption::some(42);
    /// assert!(!some_value.is_none().expose());
    ///
    /// let none_value: CtOption<i32> = CtOption::none(0);
    /// assert!(none_value.is_none().expose());
    /// ```
    pub fn is_none(&self) -> CtBool {
        !self.is_some
    }

    /// Converts an `&CtOption<T>` to a `CtOption<&T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let some_value = CtOption::some(42);
    /// let reference = some_value.as_ref();
    /// assert_eq!(reference.expose(), Some(&42));
    /// ```
    pub const fn as_ref(&self) -> CtOption<&T> {
        CtOption {
            value: &self.value,
            is_some: self.is_some,
        }
    }

    /// Converts an `&mut CtOption<T>` to a `CtOption<&mut T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let mut some_value = CtOption::some(42);
    /// if let Some(x) = some_value.as_mut().expose() {
    ///     *x = 100;
    /// }
    /// assert_eq!(some_value.expose(), Some(100));
    /// ```
    pub const fn as_mut(&mut self) -> CtOption<&mut T> {
        CtOption {
            value: &mut self.value,
            is_some: self.is_some,
        }
    }

    /// Returns the contained `Some` value or a provided default.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let some_value = CtOption::some(42);
    /// assert_eq!(some_value.unwrap_or(100), 42);
    ///
    /// let none_value: CtOption<i32> = CtOption::none(0);
    /// assert_eq!(none_value.unwrap_or(100), 100);
    /// ```
    pub fn unwrap_or(self, def: T) -> T
    where
        T: CtSelect,
    {
        T::ct_select(self.is_some, &self.value, &def)
    }

    /// Returns the contained `Some` value or a default.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let some_value = CtOption::some(42);
    /// assert_eq!(some_value.unwrap_or_default(), 42);
    ///
    /// let none_value: CtOption<i32> = CtOption::none(0);
    /// assert_eq!(none_value.unwrap_or_default(), 0);
    /// ```
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
    /// `T::Default()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let some_value = CtOption::some(5);
    /// let doubled = some_value.map(|x| x * 2);
    /// assert_eq!(doubled.expose(), Some(10));
    ///
    /// let none_value: CtOption<i32> = CtOption::none(0);
    /// let doubled_none = none_value.map(|x| x * 2);
    /// assert_eq!(doubled_none.expose(), None);
    /// ```
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

    /// Applies a closure to the inner value. Unlike `CtOption::map`, this allows one to provide
    /// the value the closure will be called on if this `CtOption` is `None`.
    /// This is very niche, but is  useful when `T` doesn't implement `Default` or when
    /// `T::default()` would be unsuitable for the operation being performed
    /// (such as when the `T::default()` is zero and when taking the inverse of a finite field element).
    ///
    /// Note that the closure is always called, even when the option is `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::{CtOption, CtSelect, CtBool};
    ///
    /// # #[derive(Debug, PartialEq, Clone, Copy)]
    /// # struct FieldElement(u32);
    /// # impl FieldElement {
    /// #     const ONE: FieldElement = FieldElement(1);
    /// #     fn invert(self) -> Self { FieldElement(1) }
    /// # }
    /// # impl CtSelect for FieldElement {
    /// #     fn ct_select(cond: CtBool, a: &Self, b: &Self) -> Self {
    /// #         FieldElement(u32::ct_select(cond, &a.0, &b.0))
    /// #     }
    /// # }
    /// let field_element = FieldElement(5);
    /// let option = CtOption::some(field_element);
    /// let inverse = option.map_with_none(|f| f.invert(), FieldElement::ONE);
    /// assert_eq!(inverse.expose(), Some(FieldElement(1)));
    /// ```
    pub fn map_with_none<U, F>(self, f: F, if_none: T) -> CtOption<U>
    where
        F: FnOnce(T) -> U,
        T: CtSelect,
    {
        self.with_none(if_none).map_unchecked(f)
    }

    /// Maps a `CtOption<T>` to a `CtOption<U>` by applying the provided closure.
    ///
    /// Note that the provided closure will be executed regardless of whether the inner value is
    /// `Some` or `None`. The primary difference between this and `CtOption::map` is that when this
    /// `CtOption` is `None`, the closure will be called on whatever value it happens to contain.
    /// This is not `unsafe` as this is guaranteed to be a well-formed value of type `T`. Still
    /// this should generally only be called after `CtOpion::with_none`
    fn map_unchecked<U, F>(self, f: F) -> CtOption<U>
    where
        F: FnOnce(T) -> U,
    {
        CtOption {
            value: f(self.value),
            is_some: self.is_some,
        }
    }

    /// Sets the inner value, only if `self` is None.
    /// This is an internal method, generally called before `map_unchecked`
    fn with_none(self, none_val: T) -> Self
    where
        T: CtSelect,
    {
        let is_some = self.is_some;
        let value = self.unwrap_or(none_val);
        CtOption { value, is_some }
    }

    /// Maps a `CtOption<T>` to `U` by applying the provided closure to a contained value,
    /// or returns the provided default value if `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let some_value = CtOption::some(5);
    /// assert_eq!(some_value.map_or(0, |x| x * 2), 10);
    ///
    /// let none_value: CtOption<i32> = CtOption::none(0);
    /// assert_eq!(none_value.map_or(100, |x| x * 2), 100);
    /// ```
    pub fn map_or<U, F>(self, default: U, f: F) -> U
    where
        U: CtSelect,
        F: FnOnce(T) -> U,
        T: Default + CtSelect,
    {
        self.map(f).unwrap_or(default)
    }

    /// Returns `None` if the option is `None`, otherwise calls the predicate with the
    /// contained value and returns `Some(t)` if the predicate returns true, otherwise `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::{CtOption, CtOrd};
    ///
    /// let some_value = CtOption::some(5);
    /// let filtered = some_value.filter(|x| x.ct_gt(&3));
    /// assert_eq!(filtered.expose(), Some(5));
    ///
    /// let too_small = CtOption::some(2);
    /// let filtered_out = too_small.filter(|x| x.ct_gt(&3));
    /// assert_eq!(filtered_out.expose(), None);
    /// ```
    #[must_use]
    pub fn filter<F>(self, f: F) -> Self
    where
        F: FnOnce(&T) -> CtBool,
        T: Default + CtSelect,
    {
        let value = self.unwrap_or_default();
        Self {
            is_some: f(&value),
            value,
        }
    }

    /// Returns `None` if the option is `None`, otherwise calls the predicate with the
    /// contained value and returns `Some(t)` if the predicate returns true, otherwise `None`.
    ///
    /// Unlike `filter`, this allows you to provide a value to use if the option is `None`
    /// instead of using `T::default()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::{CtOption, CtOrd};
    ///
    /// let some_value = CtOption::some(5);
    /// let filtered = some_value.filter_with_none(|x| x.ct_gt(&3), 0);
    /// assert_eq!(filtered.expose(), Some(5));
    ///
    /// let too_small = CtOption::some(2);
    /// let filtered_out = too_small.filter_with_none(|x| x.ct_gt(&3), 0);
    /// assert_eq!(filtered_out.expose(), None);
    /// ```
    #[must_use]
    pub fn filter_with_none<F>(self, f: F, if_none: T) -> Self
    where
        F: FnOnce(&T) -> CtBool,
        T: CtSelect,
    {
        let value = self.unwrap_or(if_none);
        Self {
            is_some: f(&value),
            value,
        }
    }

    /// Maps a `CtOption<T>` to `U` by applying the provided closure to a contained value,
    /// or returns `U::default()` if `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let some_value = CtOption::some(5);
    /// assert_eq!(some_value.map_or_default(|x| x * 2), 10);
    ///
    /// let none_value: CtOption<i32> = CtOption::none(0);
    /// assert_eq!(none_value.map_or_default(|x| x * 2), 0);
    /// ```
    pub fn map_or_default<U, F>(self, f: F) -> U
    where
        U: CtSelect + Default,
        F: FnOnce(T) -> U,
        T: CtSelect + Default,
    {
        self.map(f).unwrap_or_default()
    }

    /// Converts from `CtOption<T>` (or `&CtOption<T>`) to `CtOption<&T::Target>`.
    ///
    /// Leaves the original `CtOption` in-place, creating a new one with a reference
    /// to the original one, additionally coercing the contents via `Deref`.
    pub fn as_deref(&self) -> CtOption<&<T as Deref>::Target>
    where
        T: Deref + CtSelect,
    {
        self.as_ref().map_unchecked(Deref::deref)
    }

    /// Converts from `CtOption<T>` (or `&mut CtOption<T>`) to `CtOption<&mut T::Target>`.
    ///
    /// Leaves the original `CtOption` in-place, creating a new one containing a mutable reference
    /// to the inner type's `Deref::Target` type.
    pub fn as_deref_mut(&mut self) -> CtOption<&mut <T as Deref>::Target>
    where
        T: DerefMut + CtSelect,
    {
        self.as_mut().map_unchecked(DerefMut::deref_mut)
    }

    /// Returns `None` if the option is `None`, otherwise returns `optb`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let x = CtOption::some(2);
    /// let y: CtOption<&str> = CtOption::none("".into());
    /// assert_eq!(x.and(y).expose(), None);
    ///
    /// let x: CtOption<i32> = CtOption::none(0);
    /// let y = CtOption::some("foo");
    /// assert_eq!(x.and(y).expose(), None);
    ///
    /// let x = CtOption::some(2);
    /// let y = CtOption::some("foo");
    /// assert_eq!(x.and(y).expose(), Some("foo"));
    /// ```
    pub fn and<U>(self, optb: CtOption<U>) -> CtOption<U> {
        CtOption {
            value: optb.value,
            is_some: self.is_some & optb.is_some,
        }
    }

    /// Calls the provided closure `f` with the contained value (or `T::default()` if `None`)
    /// and returns the resulting `CtOption<U>`. The result will be `None` if this option is `None`,
    /// regardless of what `f` returns.
    ///
    /// Note that the closure `f` is always called, even when the option is `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::{CtOption, CtOrd};
    /// # fn ct_sqrt(x: u32) -> CtOption<u32> {
    /// #     CtOption::new(x / 2, x.ct_gt(&0))
    /// # }
    ///
    /// let some_value = CtOption::some(16);
    /// assert_eq!(some_value.and_then(ct_sqrt).expose(), Some(8));
    ///
    /// let none_value: CtOption<u32> = CtOption::none(0);
    /// assert_eq!(none_value.and_then(ct_sqrt).expose(), None);
    /// ```
    pub fn and_then<U, F>(self, f: F) -> CtOption<U>
    where
        F: FnOnce(T) -> CtOption<U>,
        T: CtSelect + Default,
    {
        self.map(f).flatten()
    }

    /// Calls the provided closure `f` with the contained value (or `if_none` if `None`)
    /// and returns the resulting `CtOption<U>`. The result will be `None` if this option is `None`,
    /// regardless of what `f` returns.
    ///
    /// Unlike `and_then`, this allows you to provide a value to use if the option is `None`
    /// instead of using `T::default()`. Note that the closure `f` is always called, even when
    /// the option is `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::{CtOption, CtOrd};
    /// # fn ct_sqrt(x: u32) -> CtOption<u32> {
    /// #     CtOption::new(x / 2, x.ct_gt(&0))
    /// # }
    ///
    /// let some_value = CtOption::some(16);
    /// assert_eq!(some_value.and_then_with_none(ct_sqrt, 1).expose(), Some(8));
    ///
    /// let none_value: CtOption<u32> = CtOption::none(0);
    /// assert_eq!(none_value.and_then_with_none(ct_sqrt, 1).expose(), None);
    /// ```
    pub fn and_then_with_none<U, F>(self, f: F, if_none: T) -> CtOption<U>
    where
        F: FnOnce(T) -> CtOption<U>,
        T: CtSelect,
    {
        self.with_none(if_none).map_unchecked(f).flatten()
    }

    /// Returns the option if it contains a value, otherwise returns `optb`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let x = CtOption::some(2);
    /// let y = CtOption::some(100);
    /// assert_eq!(x.or(y).expose(), Some(2));
    ///
    /// let x: CtOption<i32> = CtOption::none(0);
    /// let y = CtOption::some(100);
    /// assert_eq!(x.or(y).expose(), Some(100));
    ///
    /// let x = CtOption::some(2);
    /// let y: CtOption<i32> = CtOption::none(0);
    /// assert_eq!(x.or(y).expose(), Some(2));
    ///
    /// let x: CtOption<i32> = CtOption::none(0);
    /// let y: CtOption<i32> = CtOption::none(0);
    /// assert_eq!(x.or(y).expose(), None);
    /// ```
    #[must_use]
    pub fn or(self, optb: CtOption<T>) -> CtOption<T>
    where
        T: CtSelect,
    {
        CtOption {
            is_some: self.is_some | optb.is_some,
            value: self.unwrap_or(optb.value),
        }
    }

    /// Inserts `value` into the option, then returns a mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let mut opt = CtOption::none(0);
    /// let val = opt.insert(5);
    /// assert_eq!(*val, 5);
    /// assert_eq!(opt.expose(), Some(5));
    /// ```
    pub fn insert(&mut self, value: T) -> &mut T {
        self.value = value;
        self.is_some = CtBool::TRUE;
        &mut self.value
    }

    /// Inserts `value` into the option if it is `None`, then returns a mutable reference
    /// to the contained value.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let mut x = CtOption::none(0);
    /// let val = x.get_or_insert(5);
    /// assert_eq!(*val, 5);
    ///
    /// let mut x = CtOption::some(7);
    /// let val = x.get_or_insert(5);
    /// assert_eq!(*val, 7);
    /// ```
    pub fn get_or_insert(&mut self, value: T) -> &mut T
    where
        T: CtSelect,
    {
        self.value.ct_replace_if(!self.is_some, &value);
        &mut self.value
    }

    /// Inserts the default value into the option if it is `None`, then returns a mutable
    /// reference to the contained value.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let mut x: CtOption<i32> = CtOption::none(0);
    /// let val = x.get_or_insert_default();
    /// assert_eq!(*val, 0);
    ///
    /// let mut x = CtOption::some(7);
    /// let val = x.get_or_insert_default();
    /// assert_eq!(*val, 7);
    /// ```
    pub fn get_or_insert_default(&mut self) -> &mut T
    where
        T: CtSelect + Default,
    {
        self.value.ct_take_if(!self.is_some());
        &mut self.value
    }

    /// Takes the value out of the option, leaving a `None` in its place.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let mut x = CtOption::some(2);
    /// let y = x.take();
    /// assert_eq!(x.expose(), None);
    /// assert_eq!(y.expose(), Some(2));
    /// ```
    #[must_use]
    pub fn take(&mut self) -> CtOption<T>
    where
        T: Default,
    {
        core::mem::take(self)
    }

    /// Replaces the actual value in the option by the value given in parameter,
    /// returning the old value if present.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let mut x = CtOption::some(2);
    /// let old = x.replace(5);
    /// assert_eq!(x.expose(), Some(5));
    /// assert_eq!(old.expose(), Some(2));
    ///
    /// let mut x = CtOption::none(0);
    /// let old = x.replace(3);
    /// assert_eq!(x.expose(), Some(3));
    /// assert_eq!(old.expose(), None);
    /// ```
    #[must_use]
    pub fn replace(&mut self, value: T) -> CtOption<T> {
        core::mem::replace(
            self,
            CtOption {
                is_some: CtBool::TRUE,
                value,
            },
        )
    }

    /// Zips `self` with another `CtOption`.
    ///
    /// If `self` is `Some(s)` and `other` is `Some(o)`, this method returns `Some((s, o))`.
    /// Otherwise, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let x = CtOption::some(1);
    /// let y = CtOption::some(5);
    /// let z: CtOption<u32> = CtOption::none(0);
    ///
    /// assert_eq!(x.zip(y).expose(), Some((1, 5)));
    /// assert_eq!(x.zip(z).expose(), None);
    /// ```
    pub fn zip<U>(self, other: CtOption<U>) -> CtOption<(T, U)> {
        CtOption {
            is_some: self.is_some & other.is_some,
            value: (self.value, other.value),
        }
    }
}

impl<T, U> CtOption<(T, U)> {
    /// Unzips an option containing a tuple of two options.
    ///
    /// If `self` is `Some((a, b))`, this method returns `(Some(a), Some(b))`.
    /// Otherwise, `(None, None)` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let x = CtOption::some((1, 5));
    /// let (x1, x2) = x.unzip();
    /// assert_eq!((x1.expose(), x2.expose()), (Some(1), Some(5)));
    ///
    /// let x: CtOption<(i32, u32)> = CtOption::none((0, 0));
    /// assert_eq!(x.unzip().0.expose(), None);
    /// assert_eq!(x.unzip().1.expose(), None);
    /// ```
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
    /// Maps a `CtOption<&T>` to a `CtOption<T>` by copying the contents of the option.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let x = 12;
    /// let opt_x = CtOption::some(&x);
    /// assert_eq!(opt_x.copied().expose(), Some(12));
    /// ```
    #[must_use]
    pub const fn copied(self) -> CtOption<T>
    where
        T: Copy,
    {
        CtOption {
            is_some: self.is_some,
            value: *self.value,
        }
    }

    /// Maps a `CtOption<&T>` to a `CtOption<T>` by cloning the contents of the option.
    ///
    /// Note that this is only constant time if `T::clone` is constant time.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let x = 12;
    /// let opt_x = CtOption::some(&x);
    /// assert_eq!(opt_x.cloned().expose(), Some(12));
    /// ```
    #[must_use]
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
    /// Maps a `CtOption<&mut T>` to a `CtOption<T>` by copying the contents of the option.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let mut x = 12;
    /// let opt_x = CtOption::some(&mut x);
    /// assert_eq!(opt_x.copied().expose(), Some(12));
    /// ```
    #[must_use]
    pub const fn copied(self) -> CtOption<T>
    where
        T: Copy,
    {
        CtOption {
            is_some: self.is_some,
            value: *self.value,
        }
    }

    /// Maps a `CtOption<&mut T>` to a `CtOption<T>` by cloning the contents of the option.
    ///
    /// Note that this is only constant time if `T::clone` is constant time.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let mut x = 12;
    /// let opt_x = CtOption::some(&mut x);
    /// assert_eq!(opt_x.cloned().expose(), Some(12));
    /// ```
    #[must_use]
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
    /// Converts from `CtOption<CtOption<T>>` to `CtOption<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cnti::CtOption;
    ///
    /// let x = CtOption::some(CtOption::some(6));
    /// assert_eq!(x.flatten().expose(), Some(6));
    ///
    /// let x = CtOption::some(CtOption::none(0));
    /// assert_eq!(x.flatten().expose(), None);
    ///
    /// let x: CtOption<CtOption<i32>> = CtOption::none(CtOption::none(0));
    /// assert_eq!(x.flatten().expose(), None);
    /// ```
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
