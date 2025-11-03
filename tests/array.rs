use cnti::{CtBool, CtEq, CtSelect, CtOrd};

// Tests for fixed length arrays
#[test]
fn test_ct_select_array() {
    let a = [1u8, 2, 3, 4];
    let b = [5u8, 6, 7, 8];

    assert_eq!(CtSelect::ct_select(CtBool::TRUE, &a, &b), a);
    assert_eq!(CtSelect::ct_select(CtBool::FALSE, &a, &b), b);
}

#[test]
fn test_ct_eq_array() {
    let a = [1u8, 2, 3, 4];
    let b = [1u8, 2, 3, 4];
    let c = [1u8, 2, 3, 5];

    assert!(a.ct_eq(&b).expose());
    assert!(!a.ct_eq(&c).expose());
    assert!(a.ct_neq(&c).expose());
}

#[test]
fn test_ct_ord_array() {
    let a = [1u8, 2, 3, 4];
    let b = [1u8, 2, 3, 5];
    let c = [1u8, 2, 3, 4];

    assert!(b.ct_gt(&a).expose());
    assert!(a.ct_lt(&b).expose());
    assert!(a.ct_leq(&c).expose());
    assert!(a.ct_geq(&c).expose());
}

