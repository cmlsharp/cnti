use std::fs;
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

    /// Returns the expected constant-time instruction for this platform
    fn expected_ct_instruction(&self) -> &str {
        match self {
            Platform::X86_64LinuxGnu | Platform::I686LinuxGnu => "cmov",
            Platform::Aarch64LinuxGnu | Platform::Aarch64AppleDarwin => "csel",
        }
    }
}

/// Available test functions in the asm_functions crate
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TestFunction {
    CtGt,
    CtEq,
}

impl TestFunction {
    fn as_function_name(&self) -> &str {
        match self {
            TestFunction::CtGt => "test_ct_gt",
            TestFunction::CtEq => "test_ct_eq",
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

    /// Compiles the test functions crate and returns the assembly output for a specific function
    ///
    /// # Example
    /// ```no_run
    /// # use asm_test::{AsmTest, Platform, TestFunction};
    /// let asm = AsmTest::new(Platform::X86_64LinuxGnu)
    ///     .compile_and_inspect(TestFunction::CtSelect);
    ///
    /// assert!(asm.contains("cmov"));
    /// ```
    pub fn compile_and_inspect(&self, func: TestFunction) -> String {
        let func_name = func.as_function_name();
        // Compile the crate to assembly
        let target_triple = self.target.as_target_triple();
        let output = Command::new("cargo")
            .current_dir(&self.crate_path)
            .args([
                "rustc",
                "--release",
                "--target",
                target_triple,
                "--",
                "--emit=asm",
                "-C",
                "llvm-args=-x86-asm-syntax=intel",
                "-C",
                "no-vectorize-loops",
                "-C",
                "no-vectorize-slp",
            ])
            .output()
            .expect("Failed to compile");

        if !output.status.success() {
            eprintln!("STDOUT:\n{}", String::from_utf8_lossy(&output.stdout));
            eprintln!("STDERR:\n{}", String::from_utf8_lossy(&output.stderr));
            panic!("Compilation failed");
        }

        // Find the generated .s file
        let asm_dir = self
            .crate_path
            .join("target")
            .join(self.target.as_target_triple())
            .join("release/deps");

        let asm_files: Vec<_> = fs::read_dir(&asm_dir)
            .expect("Failed to read asm dir")
            .filter_map(|e| e.ok())
            .filter(|e| e.path().extension().map(|ext| ext == "s").unwrap_or(false))
            .collect();

        assert!(!asm_files.is_empty(), "No assembly file generated");
        let asm_file = &asm_files[0].path();

        // Read the assembly file
        let full_asm = fs::read_to_string(asm_file).expect("Failed to read asm file");

        // Extract just the function we care about
        self.extract_function_asm(&full_asm, func_name)
    }

    /// Extracts the assembly for a specific function from the full assembly output
    fn extract_function_asm(&self, full_asm: &str, func_name: &str) -> String {
        let mut in_function = false;
        let mut result = String::new();

        // Handle both Linux (test_ct_select:) and Darwin (_test_ct_select:) naming
        let start_markers = [
            format!("{func_name}:"),  // Linux style
            format!("_{func_name}:"), // Darwin style
        ];

        for line in full_asm.lines() {
            // Check if we're entering the target function
            if !in_function
                && start_markers.iter().any(|marker| line.contains(marker))
                && !line.trim().starts_with('#')
                && !line.trim().starts_with(';')
            {
                in_function = true;
                result.push_str(line);
                result.push('\n');
                continue;
            }

            if in_function {
                // Check if we've reached the next function or end of section
                let trimmed = line.trim();
                if trimmed.ends_with(':') && !trimmed.starts_with('.') && !trimmed.starts_with('L')
                {
                    // Found start of another function (non-local label), stop
                    break;
                }
                result.push_str(line);
                result.push('\n');
            }
        }

        if result.is_empty() {
            // If we didn't find the function, return the full assembly for debugging
            eprintln!(
                "Warning: Could not find function '{}' in assembly output",
                func_name
            );
            eprintln!("Returning full assembly for inspection");
            full_asm.to_string()
        } else {
            result
        }
    }
}

/// Helper to verify constant-time properties of assembly
fn verify_no_branch(asm: &str, func_name: &str, platform: Platform) {
    let asm_lower = asm.to_lowercase();

    // Verify it uses the expected constant-time instruction
    let expected = platform.expected_ct_instruction();
    assert!(
        asm_lower.contains(expected),
        "{}: should use {} instruction for constant-time operation on {:?}",
        func_name,
        expected,
        platform
    );

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

    #[test]
    fn asm_branchless_ct_gt() {
        let platforms = [
            Platform::X86_64LinuxGnu,
            Platform::Aarch64AppleDarwin,
            //Platform::Aarch64LinuxGnu,
            //Platform::I686LinuxGnu,
        ];
        let test = TestFunction::CtGt;

        for platform in platforms {
            println!("\n=== Testing on {:?} ===", platform);
            let asm = AsmTest::new(platform).compile_and_inspect(test);

            println!("Assembly:\n{}", asm);
            verify_no_branch(
                &asm,
                &format!("{} on {:?}", test.as_function_name(), platform),
                platform,
            );
        }
    }

    #[test]
    fn asm_branchless_ct_eq() {
        let platforms = [
            Platform::X86_64LinuxGnu,
            Platform::Aarch64AppleDarwin,
            //Platform::Aarch64LinuxGnu,
            //Platform::I686LinuxGnu,
        ];
        let test = TestFunction::CtEq;

        for platform in platforms {
            println!("\n=== Testing on {:?} ===", platform);
            let asm = AsmTest::new(platform).compile_and_inspect(test);

            println!("Assembly:\n{}", asm);
            verify_no_branch(
                &asm,
                &format!("{} on {:?}", test.as_function_name(), platform),
                platform,
            );
        }
    }
}
