# cnti

`cnti` is a low-level `no-std` library that provides abstractions for writing '__`c__onsta__n__t` __`ti__me`' programs (programs which do not leak information about secret data through timing side channels). It takes heavy inspiration from [subtle](https://github.com/dalek-cryptography/subtle) which itself is inspired by [rust-timing-shield](https://www.chosenplaintext.ca/open-source/rust-timing-shield/getting-started/). The goal of this project is to facilitate the writing performant constant time code. However, __this library is a complement, not a substitute, for verifying the generated assembly and empirical timing charictaristics of security-critical functions__.

This library is still a work-in-progress. 

## Usage

```rust,no_run
use cnti::{CtBool, CtEq, CtSelectExt};


// a**b (mod 2^32) where b is secret
fn pow_secret(a: u32, b: u32) -> u32 {
    let mut result = 1u32;
    for i in 0..32 {
        let bit = (b >> 1) & 1;
        result.ct_replace_if(bit.ct_eq(&1), &result.wrapping_mul(a));
        // eqvuialently: result = bit.ct_eq(&1).if_true(&result.wrapping_mul(a)).else_(&result);
        a.wrapping_mul(a);
    }
    result
}
```

## Techniques

First, a disclaimer. Preventing timing-based side-channels is [hard](https://eprint.iacr.org/2025/435.pdf) and fundamentally requires full consideration of the hardware+software stack. This library solely aims to address the very upper-most layer: allowing one to write pure Rust code that compiles to assembly which does not branch on secret data. However, even this is easier said than done. There is fundamentally no way for `rustc` (or indeed any compiler backed by LLVM) to guarantee that code will not be optimized in such a way that branches on secret data are introduced (though there have been [proposals](https://discourse.llvm.org/t/rfc-constant-time-coding-support/87781) to this effect). As such any techniques that this, or any other, library employs may cease to work in future versions of `rustc` or LLVM without notice (and as such, one should consider fixing a particular version of the compiler in security-critical applications).

But we have to make the best of the world we live in while we are living in it. To this end, `cnti` employs a few techniques to (hopefully) prevent LLVM from optimizing branchless code into assembly that branches.

* Avoiding the `bool` type as much as possible. When LLVM knows that a value is constrained to 0 or 1, it will sometimes perform niche optimizations which convert seemingly branchless code into a branch. The classic [example](https://rust.godbolt.org/z/W39oGY1hM):
    ```rust
    fn cmov(a: &mut u32, b: u32, cond: bool) {
        let mask = (-(cond as i32)).cast_unsigned();
        *a ^= *a & mask;
        *a ^= b & mask;
    }
    ```
    (at time of writing) becomes:
    ```assembly
    cmov:
            test    ecx, ecx
            jne     .LBB0_2
            mov     esi, dword ptr [rdi]
    .LBB0_2:
            mov     dword ptr [rdi], esi
            ret
    ```

    At an even more basic level, short-circuiting logical operators like `x && y || z` may also be compiled to branching code.

    `cnti::CtBool` (like `subtle::Choice` and `timing_shield::TpBool`) internally represent a `bool` as a `u8`. However, merely casting a `bool` to a `u8` is insufficient (the compiler can just as easily tell that `cond & 1` is effectively a boolean). As such all of these libraries utilize some kind of 'optimization barrier'. Speaking of..


* `core::hint::black_box`: This is a compiler hint that suggests to `rustc` that it should treat the result of certain expressions as a 'black box' and (attempt to) prevent LLVM from making optimization based on it. Note that the docs for this function contains the warning (emphasis theirs)
    > Note however, that `black_box` is only (and can only be) provided on a “best-effort” basis. The extent to which it can block optimisations may vary depending upon the platform and code-gen backend used. Programs cannot rely on `black_box` for correctness, beyond it behaving as the identity function. As such, __it must not be relied upon to control critical program behavior__. This also means that this function does not offer any guarantees for cryptographic or security purposes.
    >
    > This limitation is not specific to `black_box`; there is no mechanism in the entire Rust language that can provide the guarantees required for constant-time cryptography. (There is also no such mechanism in LLVM, so the same is true for every other LLVM-based compiler.)
    
    The wording in this warning [used to be scarier](https://github.com/rust-lang/rust/pull/126703). Understandably, the Rust team does not want to make security guarantees which it is fundamentally impossible for them to make. However, this pushed people away from using `black_box` in favor of other tricks such as `core::ptr::read_volatile` and empty `core::arch::asm!` blocks. However, these make precisely the same formal gurantees that `black_box` makes (which is to say none). Per [these](https://rust-lang.zulipchat.com/#narrow/channel/122651-general/topic/black_box.20and.20crypto/with/349120959) [threads](https://rust-lang.zulipchat.com/#narrow/channel/146212-t-compiler.2Fconst-eval/topic/const.20ptr.3A.3Aread_volatile), `black_box` appears to be the least-worst option in terms of 'guarantees' (where 'guarantee' here means 'hope that we will not be smited by the LLVM gods for our huburis'). It also has the benefit of being permitted in `const` contexts.

* Inline-assembly blocks to guarantee `cmov`/`csel` instructions where available. This crate makes use of the `cmov` crate, which provides guaranteed `cmov` and `csel` instructions on x86 and ARM respectively, while providing utilizing a bit-wise fallback on other platforms (note that no optimization barrier is employed by the `cmov` crate in those cases, but this is covered by `cnti`'s use of `black_box`). Note that while LLVM has explicit passes dedicated to (sometimes) replacing `cmov` instructions with branches, at present it leaves inline assembly blocks alone. This provides more efficient assembly for conditional assignment than an optimization barrier + bitwise ops does. In the future, I plan on adding some `asm!` blocks to ensure e.g. `cmp`+`setg` instructions are used for integer comparisons provided by the `cnti::CtOrd` trait as well.

## Comparisons with `subtle`

`subtle` is undoubtedly the state-of-the-art in this space, and this crate takes a ton of inspiration from it. At a high level, this crate provides essentially the same abstractions that `subtle` does with some ergonomic and performance improvements.

* `cnti::CtBool` is essentially equivalent to `subtle::Choice`
    * However, because `cnti` utilizes `core::hint::black_box` (see above) as its optimization barrier, `CtBool`'s can be constructed/converted back into `bool`s in `const` contexts. The lack of this feature in `subtle` led `crypto-bigint` to essentially [re-implement](https://docs.rs/crypto-bigint/latest/crypto_bigint/struct.ConstChoice.html) `subtle::Choice` (sans _any_ optimization barrier at all).  Note that `subtle` has a feature flag to enable using `core::hint::black_box`, at time of writing, enabling it simply causes a compiler error because the main `black_box` function is not conditionally disabled, resulting in duplicate function definitions. 
* `cnti::CtSelect` replaces `subtle::ConditionallySelectable`.
    * As discussed above, the implementation for `cnti::CtSelect` for primtive integer types uses the `cmov`. Along with `core::hint::black_box` (which does not require an additional `#[inline(never)]` helper function and thereby the cost of a function call), this yields considerably better codegen. Consider this example of a function which returns one of two values depending on an equality test.
        ```assembly
        cnti_select_if_eq:
            mov eax, esi
            cmp esi, edx
            sete byte ptr [rsp - 1]
            lea rcx, [rsp - 1]
            movzx ecx, byte ptr [rsp - 1]
            test cl, cl
            cmovne eax, edi
            ret
        ```
        vs.

        ```assembly
        subtle_select_if_eq:
            push rbp
            push rbx
            push rax
            mov ebx, esi
            mov ebp, edi
            xor edi, edi
            cmp edx, esi
            sete dil
            call subtle::black_box
            movzx eax, al
            neg eax
            xor ebp, ebx
            and ebp, eax
            xor ebp, ebx
            mov eax, ebp
            add rsp, 8
            pop rbx
            pop rbp
            ret

        subtle::black_box:
                mov byte ptr [rsp - 1], dil
                movzx eax, byte ptr [rsp - 1]
                ret
        ```
        Note that `cnti`'s assembly is not perfect either. The use of an optimization barrier comes at the cost of an extra unnecessary store and load of the comparison result from memory.

    * `subtle::ConditionallySelectable` has `Copy` as a super-trait, severely restricting which types it can be implemented for. Meanwhile, `cnti::CtSelect` requires only that implementors be `Sized`. * While both traits are defined by a static `ct_select` method, `cnti` adds methods to `CtBool` that permits doing selection via `cond.if_true(&x).else_(&y)`. In my opinion, this makes it easier to differentiate which branch is which compared to `T::conditional_select(&y, &x, cond)` (when writing this, I found myself accidentally reversing the order). 

* `cnti::CtOrd` replaces `subtle::ConstantTimeGreater` + `subtle::ConstantTimeLess`:
    * The `subtle` implementation of a constant-time greater-than comparison is quite slow. Compare the `cnti` implementation of the greater-than operator for `u64`s to `subtle`s''. (Note: I would like to improve `cnti`'s implementation further to simply use `cmp`+`setg`)
        ```assembly
        cnti_ct_gt:
            mov rax, rsi
            sub rax, rdi
            not rsi
            mov rcx, rdi
            and rcx, rsi
            xor rsi, rdi
            and rsi, rax
            or rsi, rcx
            shr rsi, 63
            mov byte ptr [rsp - 1], sil
            lea rax, [rsp - 1]
            movzx eax, byte ptr [rsp - 1]
            ret

        subtle_ct_gt:
            mov rax, rdi
            not rax
            and rax, rsi
            mov rcx, rax
            shr rcx
            or rcx, rax
            mov rax, rcx
            shr rax, 2
            or rax, rcx
            mov rcx, rax
            shr rcx, 4
            or rcx, rax
            mov rax, rcx
            shr rax, 8
            or rax, rcx
            mov rcx, rax
            shr rcx, 16
            or rcx, rax
            or rsi, rcx
            shr rcx, 32
            or rcx, rsi
            not rcx
            and rcx, rdi
            mov rax, rcx
            shr rax
            or rax, rcx
            mov rcx, rax
            shr rcx, 2
            or rcx, rax
            mov rax, rcx
            shr rax, 4
            or rax, rcx
            mov rcx, rax
            shr rcx, 8
            or rcx, rax
            mov rax, rcx
            shr rax, 16
            or rax, rcx
            mov rcx, rax
            shr rcx, 32
            or ecx, eax
            and cl, 1
            movzx edi, cl
            jmp subtle::black_box

        subtle::black_box:
            mov byte ptr [rsp - 1], dil
            movzx eax, byte ptr [rsp - 1]
            ret
        ```
    * `cnti`'s `CtOrd` trait is significantly more full featured than `subtle::ConstantTimeGreater` + `subtle::ConstantTimeLess`. `cnti::CtOrd` includes (with default implementations) `ct_leq`, `ct_geq` as well as `ct_min`, `ct_max` and `ct_clamp` for types that also implement `CtSelect`.
    * `cnti` includes implementations of this trait for signed integers while `subtle` does not.
    * `CtOrd` provides a derive macro for structs:
        ```rust,ignore
        use cnti::{CtOrd, CtBool, CtEq};

        #[derive(CtOrd)]
        struct MyStruct {
            x: i32,
            y: u32,
        }

        // expands into
        impl CtOrd for MyStruct {
            fn ct_gt(&self, other: &Self) -> cnti::CtBool {
                let eq_x = self.x.ct_eq(&other.x);
                let gt_x = self.x.ct_gt(&other.x);
                let gt_y = self.y.ct_gt(&other.y);
                gt_x | (eq_x & gt_y)
            }
        }

        ```

* `cnti::CtEq` is analogous to `subtle::ConstantTimeEq`.
    * Like the above traits, `cnti` provides a derive macro for `CtEq`:
        ```rust,ignore
        use cnti::{CtEq, CtBool};

        #[derive(CtEq)]
        struct MyStruct {
            x: usize,
            y: i8,
        }

        // expands into:
        impl CtEq for MyStruct {
            fn ct_eq(&self, other: &Self) -> CtBool {
                self.x.ct_eq(&other.x) & self.y.ct_eq(&other.y)
            }
        }
        ```
* `cnti::CtOption` is a direct analogue to `subtle::CtOption` with the following changes:
    * Constructable in const contexts 
    * Provides analogues for nearly every method that Rust's standard `Option` has.
    * Addresses [dalek-cryptography/subtle#63](https://github.com/dalek-cryptography/subtle/issues/63) by providing an alternatives to `CtOption::map` (namely, instead allow the user to explicitly provide a value for the closure to be called on in the case that the `CtOption` is `None`.

* Minor differences:
    * Unlike `subtle`, `cnti` does not implement `CtEq` and `CtOrd` for `[T]` (though it does for `[T; N]`) since this inherently involves leaking the length of the slice via timing. However, `cnti` allows the programmer to explicitly opt into this behavior by casting their slice to a `PublicLenSlice<T>` via `PublicLenSlice::from_slice(val)`. `PublicLenSlice` does implement `CtEq` and `CtOrd`.
    * `cnti` generally shies away from providing implementations along the lines of `From<ConstantTimeType> for Type`. This is because these types of "exposing" conversions generally warrent documentation with big warning messages, but documentation on trait _implementations_ is not displayed prominently in rustdoc (and, as a matter of taste, the operation that potentially leaks a value should not be accessibly via a method as generic as `.into()`). Instead these conversions are performed explicitly via the methods `CtBool::expose` and `CtOption::expose`.
    * This crate includes unit tests that compile core functions to assembly on platforms of interest and ensures the result is branchless.

### Benefits of subtle over this crate:
* `subtle` is the state of the art, and battle tested. You should trust the people who wrote `subtle` to write correct stuff more than you trust me.
* `subtle` supports  older versions of rust than this crate does. `subtle`
* `subtle` supports versions of Rust as early as 1.41. This crate at least requires 1.59 because of its dependency on the `cmov` crate.


## Performance

TODO: concrete benchmarks


