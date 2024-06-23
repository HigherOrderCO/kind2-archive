use std::process::Command;
use std::path::PathBuf;

fn main() {
  let kindc_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .join("target")
    .join("kindc");

  let args: Vec<String> = std::env::args().skip(1).collect();

  Command::new(kindc_path)
    .args(&args)
    .status()
    .expect("Failed to run kindc");
}

