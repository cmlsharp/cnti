use crate::{CtBool, CtEq, CtOrd, CtSelect};
use core::hint;
use core::ops::Deref;

#[repr(transparent)]
// is deriving this fine, or should i manually impl so pulling stuff out of blackbox goes through
// expose?
#[derive(Clone, Copy, Default)]
/// Puts T behind a core::hint::black_box optimization barrier.
/// Note that this is just a best effort attempt to prevent LLVM from making
/// non-constant-time optimizations wrt T. The compiler is technically free to ignore this.
/// Assembly should always be manually verified.
pub struct BlackBox<T>(T);

impl<T: CtEq> CtEq for BlackBox<T> {
    fn ct_eq(&self, other: &Self) -> CtBool {
        self.deref().ct_eq(other)
    }
}

impl<T: CtOrd> CtOrd for BlackBox<T> {
    fn ct_gt(&self, other: &Self) -> CtBool {
        self.deref().ct_gt(other)
    }
}

impl<T: CtSelect> CtSelect for BlackBox<T> {
    fn ct_select(choice: CtBool, then: &Self, else_: &Self) -> Self {
        BlackBox::protect(T::ct_select(choice, then, else_))
    }
}

impl<T> core::fmt::Debug for BlackBox<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "BlackBox")
    }
}

impl<T> Deref for BlackBox<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        // does this do anything
        &self.0
    }
}

impl<T> BlackBox<T> {
    pub const fn protect(b: T) -> Self {
        // Important, this is the only public constructor for black box
        // meaning all values stored in black box have been passed through hint::black_box
        // This means (I think) we should not need to put black_box on the expose methods
        // Doing so does actually prevent LLVM from optimizing e.g. duplicate loads from the stack
        // but we'd like to allow that optimization if we can
        // So for now, I'm sticking with just having it in the constructor
        Self(hint::black_box(b))
    }

    // XXX once Destruct trait is stable, we can make this a const function probably
    pub fn expose(self) -> T {
        self.0
    }

    // TODO: deprecate once Destruct trait is stable
    pub const fn expose_const(self) -> T
    where
        T: Copy,
    {
        self.0
    }
}
