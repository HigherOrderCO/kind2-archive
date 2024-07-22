//./book/compile.rs//
//./term/compile.rs//

use clap::{Arg, ArgAction, Command};
use std::fs;
use std::path::Path;
use std::io::Write;
use std::process::Command as SysCommand;

mod book;
mod info;
mod show;
mod sugar;
mod term;

use book::*;
use info::*;
use sugar::*;
use term::*;

use highlight_error::highlight_error;
use TSPL::Parser;

TSPL::new_parser!(KindParser);

// FIXME: not necessary, already on book
fn generate_kindc(book: &Book, arg: &str) -> String {
  let book_kindc = book.to_kindc();
  let main_kindc = format!("MAIN = {};\n", Term::to_kindc_name(arg));
  format!("{}{}", book_kindc, main_kindc)
}

fn run_kindc(book: &Book, cmd: &str, file: &str) -> (Vec<Info>, String) {
  let kindc_content = generate_kindc(book, file);
  let mut temp_file = fs::File::create(".main.kindc").expect("Failed to create '.main.kindc'.");
  temp_file.write_all(kindc_content.as_bytes()).expect("Failed to write '.main.kindc'.");
  let output = SysCommand::new("kindc").arg(cmd).arg(".main.kindc").output().expect("Failed to execute kindc command");
  let stdout = String::from_utf8_lossy(&output.stdout);
  let stderr = String::from_utf8_lossy(&output.stderr);
  (Info::parse_infos(&stdout), stderr.to_string())
}

fn check(name: &str) {
  let book = load_book(name);
  let (infos, stderr) = run_kindc(&book, "check", name);
  for info in &infos {
    println!("{}", info.pretty(&book));
  }
  if stderr.is_empty() && infos.is_empty() {
    println!("Checked.");
  }
  eprintln!("{stderr}");
}

fn normal(name: &str, _level: u32) {
  let book = load_book(name);
  let (infos, stderr) = run_kindc(&book, "run", name);
  for info in &infos {
    println!("{}", info.pretty(&book));
  }
  eprintln!("{stderr}");
}

fn load_book(name: &str) -> Book {
  let cwd = std::env::current_dir().expect("failed to get current directory");
  Book::boot(cwd.to_str().unwrap(), name).unwrap_or_else(|e| {
    eprintln!("{e}");
    std::process::exit(1);
  })
}

fn deps(name: &str) {
  let mut book = Book::new();
  let cwd = std::env::current_dir().expect("failed to get current directory");
  if let Err(e) = book.load(cwd.to_str().unwrap(), name) {
    eprintln!("{e}");
    std::process::exit(1);
  }
  for dep in book.defs.keys() {
    println!("{}", dep);
  }
}

fn compile_to_kindc(name: &str) {
  let book = load_book(name);
  let code = generate_kindc(&book, name);
  println!("{code}");
}

fn compile_to_js(name: &str) {
  let book = load_book(name);
  let code = book.to_js();
  println!("{}", code);
}

fn strip_extension(filename: &str) -> String {
    Path::new(filename)
        .with_extension("")
        .to_str()
        .unwrap_or(filename)
        .to_string()
}

fn main() {
  let matches = Command::new("kind2")
    .about("The Kind2 Programming Language")
    .subcommand_required(true)
    .arg_required_else_help(true)
    .subcommand(Command::new("check")
      .about("Type-checks a term")
      .arg(Arg::new("name").required(true)))
    .subcommand(Command::new("normal")  
      .about("Normalizes a term")
      .arg(Arg::new("name").required(true))
      .arg(Arg::new("level")
        .long("level")
        .short('l')
        .action(ArgAction::Set)
        .value_parser(clap::value_parser!(u32))))
    .subcommand(Command::new("deps")
      .about("Lists all dependencies of a symbol")
      .arg(Arg::new("name").required(true)))
    .subcommand(Command::new("to-kindc")
      .about("Compiles to KINDC")  
      .arg(Arg::new("name").required(true)))
    .subcommand(Command::new("to-js")
      .about("Compiles to JavaScript")
      .arg(Arg::new("name").required(true)))
    .get_matches();

  match matches.subcommand() {
    Some(("check", sub_matches)) => {
      let name = strip_extension(sub_matches.get_one::<String>("name").expect("required"));
      check(&name);
    }
    Some(("normal", sub_matches)) => {
      let name = strip_extension(sub_matches.get_one::<String>("name").expect("required"));
      let level = sub_matches.get_one::<u32>("level").copied().unwrap_or(0);
      normal(&name, level);
    }
    Some(("deps", sub_matches)) => {
      let name = strip_extension(sub_matches.get_one::<String>("name").expect("required"));
      deps(&name);
    }
    Some(("to-kindc", sub_matches)) => {
      let name = strip_extension(sub_matches.get_one::<String>("name").expect("required"));
      compile_to_kindc(&name);
    }
    Some(("to-js", sub_matches)) => {
      let name = strip_extension(sub_matches.get_one::<String>("name").expect("required"));
      compile_to_js(&name);
    }
    _ => unreachable!(),
  }
}
