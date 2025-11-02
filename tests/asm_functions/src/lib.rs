use cnti::{CtEq, CtOrd, CtSelectExt};

#[unsafe(no_mangle)]
#[inline(never)]
pub fn test_ct_gt(a: &mut u32, b: u32, c: u32) {
    a.ct_replace_if(&b, b.ct_gt(&c));
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn test_ct_eq(a: &mut u32, b: u32, c: u32) {
    a.ct_replace_if(&b, b.ct_eq(&c));
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn test_multi_ct_gt(a: &mut u32, b: [u32; 3], c: [u32; 3]) {
    let cond = b[0].ct_gt(&c[0]) & b[1].ct_gt(&c[1]) & b[2].ct_gt(&c[2]);
    a.ct_replace_if(&b[0], cond);
}
