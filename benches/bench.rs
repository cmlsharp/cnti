use core::hint::black_box;
use criterion::{Criterion, criterion_group, criterion_main};

fn gt_u64_bench(c: &mut Criterion) {
    c.bench_function("gt_cnti 10000", |b| {
        b.iter(|| {
            use cnti::CtOrd;
            let a = core::array::repeat::<u64, 10000>(1);
            let b = core::array::repeat::<u64, 10000>(2);
            let mut ret = cnti::CtBool::TRUE;
            for (a_i, b_i) in a.into_iter().zip(b.into_iter()) {
                ret &= black_box(a_i).ct_gt(&black_box(b_i))
            }
        });
    });
    c.bench_function("gt_subtle 10000", |b| {
        b.iter(|| {
            use subtle::ConstantTimeGreater;
            let a = core::array::repeat::<u64, 10000>(1);
            let b = core::array::repeat::<u64, 10000>(2);
            let mut ret = subtle::Choice::from(1u8);
            for (a_i, b_i) in a.into_iter().zip(b.into_iter()) {
                ret &= black_box(a_i).ct_gt(&black_box(b_i))
            }
        });
    });
}

fn eq_u64_bench(c: &mut Criterion) {
    c.bench_function("eq_cnti 10000", |b| {
        b.iter(|| {
            use cnti::CtEq;
            let a = core::array::repeat::<u64, 10000>(1);
            let b = core::array::repeat::<u64, 10000>(2);
            let mut ret = cnti::CtBool::TRUE;
            for (a_i, b_i) in a.into_iter().zip(b.into_iter()) {
                ret &= black_box(a_i).ct_eq(&black_box(b_i))
            }
        });
    });
    c.bench_function("eq_subtle 10000", |b| {
        b.iter(|| {
            use subtle::ConstantTimeEq;
            let a = core::array::repeat::<u64, 10000>(1);
            let b = core::array::repeat::<u64, 10000>(2);
            let mut ret = subtle::Choice::from(1u8);
            for (a_i, b_i) in a.into_iter().zip(b.into_iter()) {
                ret &= black_box(a_i).ct_eq(&black_box(b_i))
            }
        });
    });
}

fn u64_max(c: &mut Criterion) {
    c.bench_function("max_cnti 10000", |b| {
        b.iter(|| {
            use cnti::CtOrd;
            let mut a = core::array::repeat::<u64, 10000>(1);
            let b = core::array::repeat::<u64, 10000>(2);
            for (a_i, b_i) in a.iter_mut().zip(b.into_iter()) {
                *a_i = black_box(&*a_i).ct_max(&black_box(b_i))
            }
        });
    });
    c.bench_function("max_subtle 10000", |b| {
        b.iter(|| {
            use subtle::ConditionallySelectable;
            use subtle::ConstantTimeGreater;
            let mut a = core::array::repeat::<u64, 10000>(1);
            let b = core::array::repeat::<u64, 10000>(2);
            for (a_i, b_i) in a.iter_mut().zip(b.into_iter()) {
                let a_i = black_box(a_i);
                let b_i = black_box(b_i);
                a_i.conditional_assign(&b_i, b_i.ct_gt(a_i));
            }
        });
    });
}

fn ct_select_u64(c: &mut Criterion) {
    c.bench_function("ct_select_cnti 10000", |b| {
        b.iter(|| {
            use cnti::CtBool;
            let mut a = black_box(core::array::repeat::<u64, 10000>(1));
            let b = black_box(core::array::repeat::<u64, 10000>(2));
            let cond = black_box(CtBool::FALSE);
            for (a_i, b_i) in a.iter_mut().zip(b.into_iter()) {
                *a_i = cond.if_true(a_i).else_(&b_i);
            }
        });
    });
    c.bench_function("conditional_select_subtle 10000", |b| {
        b.iter(|| {
            use subtle::Choice;
            use subtle::ConditionallySelectable;
            let mut a = black_box(core::array::repeat::<u64, 10000>(1));
            let b = black_box(core::array::repeat::<u64, 10000>(2));
            let cond = black_box(Choice::from(0u8));
            for (a_i, b_i) in a.iter_mut().zip(b.into_iter()) {
                *a_i = u64::conditional_select(&b_i, a_i, cond);
            }
        });
    });
}

criterion_group!(benches, gt_u64_bench, eq_u64_bench, u64_max, ct_select_u64);
criterion_main!(benches);
