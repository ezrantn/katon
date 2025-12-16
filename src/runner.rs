use std::io::Write;
use std::process::{Command, Stdio};

pub fn verify_with_z3(smt_code: &str) -> Result<(), String> {
    let mut child = Command::new("z3")
        .arg("-in") // Read from stdin
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|_| "Could not find 'z3' binary. Is it installed and in your PATH?")?;

    // 2. Write the SMT string to Z3's stdin
    {
        let stdin = child.stdin.as_mut().ok_or("Failed to open stdin")?;
        stdin
            .write_all(smt_code.as_bytes())
            .map_err(|e| e.to_string())?;
    } // stdin closes automatically here, telling Z3 "we are done writing"

    // 3. Read the output
    let output = child.wait_with_output().map_err(|e| e.to_string())?;
    let result = String::from_utf8_lossy(&output.stdout);

    println!("Z3 Output:\n{}", result);

    // We want to ensure NO "sat" appears.
    // However, "unsat" appearing inside a variable name (rare) could trick us,
    // but standard Z3 output is clean.

    // Simple check: splitting by whitespace
    for line in result.lines() {
        if line.trim() == "sat" {
            println!("❌ VERIFICATION FAILED inside the loop logic.");
            return Err("Counter-example found".to_string());
        }
    }

    if result.matches("unsat").count() > 0 {
        println!("VERIFIED! All checks passed.");
        Ok(())
    } else {
        Err("Z3 returned weird output".to_string())
    }
}
