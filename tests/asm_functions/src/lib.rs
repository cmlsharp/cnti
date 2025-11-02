use cnti::{CtEq, CtOrd, CtSelectExt};

#[unsafe(no_mangle)]
pub fn test_ct_gt(a: &mut u32, b: u32, c: u32) {
    a.ct_replace_if(&b, b.ct_gt(&c));
}

#[unsafe(no_mangle)]
pub fn test_ct_eq(a: &mut u32, b: u32, c: u32) {
    a.ct_replace_if(&b, b.ct_eq(&c));
}
