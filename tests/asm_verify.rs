use std::path::PathBuf;
use std::process::Command;

/// Target platform for compilation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Platform {
    X86_64LinuxGnu,
    Aarch64LinuxGnu,
    Aarch64AppleDarwin,
    I686LinuxGnu,
}

impl Platform {
    fn as_target_triple(&self) -> &str {
        match self {
            Platform::X86_64LinuxGnu => "x86_64-unknown-linux-gnu",
            Platform::Aarch64LinuxGnu => "aarch64-unknown-linux-gnu",
            Platform::Aarch64AppleDarwin => "aarch64-apple-darwin",
            Platform::I686LinuxGnu => "i686-unknown-linux-gnu",
        }
    }

    /// Returns list of instructions that indicate non-constant-time behavior
    fn bad_instructions(&self) -> &'static [&'static str] {
        const X86_BAD: &[&str] = &[
            "jne", "je", "jz", "jnz", "jg", "jl", "jge", "jle", "ja", "jb", "jae", "jbe", "jc",
            "jnc", "jo", "jno", "js", "jns", "jp", "jnp",
        ];

        const ARM_BAD: &[&str] = &[
            "b.eq", "b.ne", "b.cs", "b.cc", "b.mi", "b.pl", "b.vs", "b.vc", "b.hi", "b.ls", "b.ge",
            "b.lt", "b.gt", "b.le", "cbz", "cbnz", "tbz", "tbnz",
        ];

        match self {
            Platform::X86_64LinuxGnu | Platform::I686LinuxGnu => X86_BAD,
            Platform::Aarch64LinuxGnu | Platform::Aarch64AppleDarwin => ARM_BAD,
        }
    }
}

/// Available test functions in the asm_functions crate
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TestFunction {
    CtGt,
    CtEq,
    CtGtMulti,
}

impl TestFunction {
    fn as_function_name(&self) -> &str {
        match self {
            TestFunction::CtGt => "test_ct_gt",
            TestFunction::CtEq => "test_ct_eq",
            TestFunction::CtGtMulti => "test_multi_ct_gt",
        }
    }
}

/// Compiles test functions and returns assembly for inspection
pub struct AsmTest {
    target: Platform,
    crate_path: PathBuf,
}

impl AsmTest {
    pub fn new(target: Platform) -> Self {
        let crate_path = PathBuf::from("tests/asm_functions");
        Self { target, crate_path }
    }

    /// Generates assembly for a specific function using cargo asm
    ///
    /// # Example
    /// ```no_run
    /// # use asm_test::{AsmTest, Platform, TestFunction};
    /// let asm = AsmTest::new(Platform::X86_64LinuxGnu)
    ///     .compile_and_inspect(TestFunction::CtGt);
    ///
    /// assert!(asm.contains("cmov"));
    /// ```
    pub fn compile_and_inspect(&self, func: TestFunction) -> String {
        let func_name = func.as_function_name();
        let target_triple = self.target.as_target_triple();

        // Use cargo asm to generate assembly for the specific function
        let output = Command::new("cargo")
            .current_dir(&self.crate_path)
            .args(["asm", "--release", "--target", target_triple, func_name])
            .output()
            .expect("Failed to run cargo asm");

        if !output.status.success() {
            eprintln!("STDOUT:\n{}", String::from_utf8_lossy(&output.stdout));
            eprintln!("STDERR:\n{}", String::from_utf8_lossy(&output.stderr));
            panic!("cargo asm failed");
        }

        String::from_utf8(output.stdout).expect("Invalid UTF-8 in assembly output")
    }
}

/// Helper to verify constant-time properties of assembly
fn verify_no_branch(asm: &str, func_name: &str, platform: Platform) {
    let asm_lower = asm.to_lowercase();

    // Verify no bad instructions (branches, conditional jumps, etc.)
    for bad_instr in platform.bad_instructions() {
        assert!(
            !asm_lower.contains(bad_instr),
            "{}: Found non-constant-time instruction '{}' on {:?}!",
            func_name,
            bad_instr,
            platform
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn asm_branchless(platform: Platform, test_fun: TestFunction) {
        let asm = AsmTest::new(platform).compile_and_inspect(test_fun);

        println!(
            "\n=== {} on {:?} === \n{}",
            test_fun.as_function_name(),
            platform,
            asm
        );
        verify_no_branch(
            &asm,
            &format!("{} on {:?}", test_fun.as_function_name(), platform),
            platform,
        );
    }

    #[test]
    fn asm_branchless_ct_gt_x86() {
        asm_branchless(Platform::X86_64LinuxGnu, TestFunction::CtGt);
    }

    #[test]
    fn asm_branchless_ct_gt_aarch_darwin() {
        asm_branchless(Platform::Aarch64AppleDarwin, TestFunction::CtGt);
    }

    #[test]
    fn asm_branchless_ct_eq_x86() {
        asm_branchless(Platform::X86_64LinuxGnu, TestFunction::CtEq);
    }

    #[test]
    fn asm_branchless_ct_eq_aarch_darwin() {
        asm_branchless(Platform::Aarch64AppleDarwin, TestFunction::CtEq);
    }

    #[test]
    fn asm_branchless_multi_ct_gt_x86() {
        asm_branchless(Platform::X86_64LinuxGnu, TestFunction::CtGtMulti)
    }

    #[test]
    fn asm_branchless_multi_ct_aarch_darwin() {
        asm_branchless(Platform::Aarch64AppleDarwin, TestFunction::CtGtMulti)
    }
}
