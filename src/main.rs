#![allow(dead_code)]
#![allow(unused_imports)]

mod book;
mod form;
mod info;
mod term;

use book::{*};
use form::{*};
use info::{*};
use term::{*};

use TSPL::Parser;
use highlight_error::highlight_error;
use std::env;
use std::fs::File;
use std::io::Write;
use std::process::Command;

TSPL::new_parser!(KindParser);

fn generate_check_hvm1(book: &Book, command: &str, arg: &str) -> String {
  //let used_defs = book.defs.keys().collect::<Vec<_>>().iter().map(|name| format!("(Pair \"{}\" Book.{})", name, name)).collect::<Vec<_>>().join(" ");
  let kind_hvm1 = include_str!("./kind2.hvm1");
  let book_hvm1 = book.to_hvm1();
  let main_hvm1 = match command {
    "check" => format!("Main = (API.check Book.{})\n", arg),
    //"check" => format!("Main = (API.check.many [{}])\n", used_defs),
    "run"   => format!("Main = (API.normal Book.{})\n", arg),
    _       => panic!("invalid command"),
  };
  let hvm1_code = format!("{}\n{}\n{}", kind_hvm1, book_hvm1, main_hvm1);
  return hvm1_code;
}

fn generate_check_hs(book: &Book, command: &str, arg: &str) -> String {
  let kind_hs = include_str!("./kind2.hs");
  let kind_hs = kind_hs.lines().filter(|line| !line.starts_with("xString")).collect::<Vec<_>>().join("\n");
  let book_hs = book.to_hs();
  let main_hs = match command {
    "check" => format!("main = (apiCheck {})\n", Term::to_hs_name(arg)),
    "run"   => format!("main = (apiNormal {})\n", Term::to_hs_name(arg)),
    _       => panic!("invalid command"),
  };
  let hs_code = format!("{}\n{}\n{}", kind_hs, book_hs, main_hs);
  return hs_code;
}

fn main() {
  let args: Vec<String> = env::args().collect();

  if args.len() < 3 {
    show_help();
  }

  let cmd = &args[1];
  let arg = &args[2];

  //println!("loading");
  match cmd.as_str() {
    "check" | "run" => {
      match Book::load(arg) {
        Ok(book) => {
          // Auto-formats the definition.
          //let defn = book.defs.get(arg).unwrap();
          //let form = book.format_def(arg, defn).flatten(60);

          // Overwrites the original file with the formatted version.
          //File::create(&format!("./{}.kind2", arg))
            //.and_then(|mut file| file.write_all(form.as_bytes()))
            //.unwrap_or_else(|_| panic!("Failed to auto-format '{}.kind2'.", arg));

          // Generates the HVM1 checker.
          //let check_hvm1 = generate_check_hvm1(&book, cmd, arg);
          //let mut file = File::create(".check.hvm1").expect("Failed to create '.check.hvm1'.");
          //file.write_all(check_hvm1.as_bytes()).expect("Failed to write '.check.hvm1'.");

          // Calls HVM1 and get outputs.
          // FIXME: re-enable HVM version
          //let output = Command::new("hvm1").arg("run").arg("-t").arg("1").arg("-c").arg("-f").arg(".check.hvm1").arg("(Main)").output().expect("Failed to execute command");
          //let stdout = String::from_utf8_lossy(&output.stdout);
          //let stderr = String::from_utf8_lossy(&output.stderr);
          
          // Generates the Haskell checker.
          let check_hs = generate_check_hs(&book, cmd, arg);
          let mut file = File::create(".check.hs").expect("Failed to create '.check.hs'.");
          file.write_all(check_hs.as_bytes()).expect("Failed to write '.check.hs'.");

          // Calls GHC and get outputs.
          let output = Command::new("runghc").arg(".check.hs").output().expect("Failed to execute command");
          let stdout = String::from_utf8_lossy(&output.stdout);
          let stderr = String::from_utf8_lossy(&output.stderr);

          // Parses and print stdout infos.
          let infos = Info::parse_infos(&stdout);
          for info in &infos {
            println!("{}", info.pretty(&book))
          }
          if infos.len() == 0 {
            println!("check!");
          }

          // Prints stdout errors and stats.
          eprintln!("{}", stderr);
        },
        Err(e) => {
          eprintln!("{}", e);
          std::process::exit(1);
        },
      }
    },
    _ => {
      show_help();
    },
  }
}

//fn main() {
  //env::set_current_dir("./book").expect("Failed to change directory to ./book");
  //let adt = term::sugar::ADT::load("Bool");
  //println!("{:?}", adt);
//}

fn show_help() {
  eprintln!("Usage: kind2 [check|run] <name>");
  std::process::exit(1);
}
