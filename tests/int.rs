use cnti::{CtBool, CtEq, CtOrd, CtSelect};
use paste::paste;
use quickcheck_macros::quickcheck;

macro_rules! test_ct_select {
        ($($t:path),*) => {
            $(paste! {
                #[quickcheck]
                fn [<test_ct_select_$t>](select: bool, a: $t, b: $t) {
                    assert_eq!(
                        CtSelect::ct_select(CtBool::protect(select), &a, &b),
                        if select { a } else { b }
                    );
                }

            })*
        };
    }

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
