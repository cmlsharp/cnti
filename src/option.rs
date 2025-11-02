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
