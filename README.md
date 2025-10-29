# cnti

This is a work-in-progress low-level library for use in constant time cryptographic implementations.

**This library is not ready for use.** Use [subtle](https://github.com/dalek-cryptography/subtle).

Takes _heavy_ inspiration from [subtle](https://github.com/dalek-cryptography/subtle) but with some improvements:
* Functions are declared `const` where possible,
* Procedural macros for deriving `CtPartialEq`, `CtEq`, `CtSelect` and `CtOrd` on structs.
* Utilizes the `cmov` crate on architectures that support it, falling back to `core::hint::black_box` when we can't. While guaranteeing constant time operations with LLVM is fundamentally impossible (without even getting into hardware), this should provide strictly better guarantees than the volatile read method used in `subtle` (additionally, `core::hint::black_box` is a const fn while `core::ptr::read_volatile` never will be).
* The traits exported by this crate have weaker super trait requirements (e.g. `CtSelect` merely requires Sized, not Copy).
* `CtOption` is nearly as fully featured as `Option` is (to the extent it can be).

`subtle` will always support earlier versions of Rust than this crate will however.
