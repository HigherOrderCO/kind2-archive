use std::process::Command;
use std::env;
//use std::path::Path;

fn main() {
    let out_dir = env::current_dir().unwrap();
    let dest_path = out_dir.join("target").join("kindc");
    
    let status = Command::new("ghc")
        .args(&["-O2", "-o", dest_path.to_str().unwrap(), "src/kindc.hs"])
        .status()
        .expect("Failed to execute GHC");

    if !status.success() {
        panic!("GHC compilation failed");
    }

    println!("cargo:rerun-if-changed=src/kindc.hs");
}
