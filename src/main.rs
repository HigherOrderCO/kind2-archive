// PROJECT FILES:
//./term/mod.rs//
//./term/show.rs//
//./term/parse.rs//
//./term/compile.rs//
//./sugar/mod.rs//
//./show/mod.rs//
//./info/mod.rs//
//./info/parse.rs//
//./info/show.rs//
//./book/mod.rs//
//./book/compile.rs//
//./book/parse.rs//
//./book/show.rs//

// PROJECT CLI (main.rs):

use clap::{Arg, ArgAction, Command};
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command as SysCommand;

mod book;
mod info;
mod show;
mod sugar;
mod term;

use book::*;
use info::*;
use show::*;
use sugar::*;
use term::*;

use highlight_error::highlight_error;
use TSPL::Parser;

TSPL::new_parser!(KindParser);

fn generate_check_hvm2(book: &Book, command: &str, arg: &str) -> String {
  let kind_hvm2 = include_str!("./kind2.hvm2");
  let book_hvm2 = book.to_hvm2_checker();
  let main_hvm2 = match command {
    "check" => format!("main = (apiCheck Book.{})\n", arg),
    "run"   => format!("main = (apiNormal Book.{})\n", arg),
    _       => panic!("invalid command"),
  };
  format!("{}\n{}\n{}", kind_hvm2, book_hvm2, main_hvm2)
}

fn generate_check_hs(book: &Book, command: &str, arg: &str) -> String {
  let kind_hs = include_str!("./kind2.hs")
    .lines()
    .filter(|line| !line.starts_with("xString"))
    .collect::<Vec<_>>()
    .join("\n");
  let book_hs = book.to_hs_checker();
  let main_hs = match command {
    "check" => format!("main = (apiCheck {})\n", Term::to_hs_name(arg)),
    "run"   => format!("main = (apiNormal {})\n", Term::to_hs_name(arg)),
    _       => panic!("invalid command"),
  };
  format!("{}\n{}\n{}", kind_hs, book_hs, main_hs)
}

fn generate_hvm2(book: &Book, arg: &str) -> String {
  let book_hvm2 = book.to_hvm2();
  let main_hvm2 = format!("main = {}\n", Term::to_hvm2_name(arg));
  format!("{}\n{}", book_hvm2, main_hvm2)
}

fn run_kore(book: &Book, cmd: &str, file: &str, runtime: &str) -> (Vec<Info>, String) {
  let command = match runtime {
    "hs" => {
      let check_hs = generate_check_hs(&book, cmd, file);
      let mut file = fs::File::create(".check.hs").expect("Failed to create '.check.hs'.");
      file.write_all(check_hs.as_bytes()).expect("Failed to write '.check.hs'.");
      SysCommand::new("runghc").arg(".check.hs").output().expect("Failed to execute command")
    }
    "hvm2" => {
      let check_hvm2 = generate_check_hvm2(&book, cmd, file);
      let mut file = fs::File::create(".check.hvm2").expect("Failed to create '.check.hvm2'.");
      file.write_all(check_hvm2.as_bytes()).expect("Failed to write '.check.hvm2'.");
      SysCommand::new("hvml").arg("run").arg("-L").arg(".check.hvm2").output().expect("Failed to execute command")
    }
    _ => panic!("invalid runtime"),
  };

  let stdout = String::from_utf8_lossy(&command.stdout);
  let stderr = String::from_utf8_lossy(&command.stderr);

  (Info::parse_infos(&stdout), stderr.to_string())
}

fn check(name: &str, runtime: &str) {
  let book = load_book(name);
  let (infos, stderr) = run_kore(&book, "check", name, runtime);

  for info in &infos {
    println!("{}", info.pretty(&book));
  }

  if stderr.is_empty() && infos.is_empty() {
    println!("check!");
  }

  eprintln!("{stderr}");
}

fn normal(name: &str, _level: u32, runtime: &str) {
  let book = load_book(name);
  let (infos, stderr) = run_kore(&book, "run", name, runtime);

  for info in &infos {
    println!("{}", info.pretty(&book));
  }

  eprintln!("{stderr}");
}

fn auto_format(file_name: &str) {
  let base = std::env::current_dir().expect("failed to get current directory");
  let file = base.join(format!("{file_name}.kind2"));
  let text = std::fs::read_to_string(&file).expect("failed to read file");
  let fid  = Book::new().get_file_id(&file.to_str().unwrap().to_string());
  let book = KindParser::new(&text).parse_book(file_name, fid).expect("failed to parse book");
  let form = book.defs.iter().map(|(name, term)| book.format_def(name, term)).collect();
  let form = Show::pile("\n\n", form).flatten(Some(60));
  std::fs::write(&file, form).expect(&format!("failed to write to file '{}'", file_name));
}

fn compile(name: &str) {
  let book = load_book(name);
  let code = generate_hvm2(&book, name);
  println!("{code}");
}

fn compare_runtimes() {
  let book_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("book");
  let mut paths: Vec<_> = fs::read_dir(&book_dir)
    .expect("failed to read book directory")
    .map(|r| r.expect("failed to read entry").path())
    .filter_map(|r| r.extension().is_some_and(|e| e == "kind2").then_some(r))
    .collect();
  paths.sort();

  for path in paths {
    let name = path.file_stem().unwrap().to_str().unwrap();

    let Some(book) = Book::boot(book_dir.to_str().unwrap(), name).ok() else {
      continue;
    };

    print!("{name:<30}: ");

    for rt in ["hs", "hvm2"] {
      std::io::stdout().flush().expect("failed to flush stdout");
      let (infos, stderr) = run_kore(&book, "check", name, rt);
      if stderr.is_empty() {
        if infos.is_empty() {
          print!("\x1b[32;1m+\x1b[0m ");
        } else {
          print!("\x1b[31;1m-\x1b[0m ");
        }
      } else {
        print!("\x1b[33;1m*\x1b[0m ");
      }
    }

    println!();
  }
}

fn load_book(name: &str) -> Book {
  let cwd = std::env::current_dir().expect("failed to get current directory");
  Book::boot(cwd.to_str().unwrap(), name).unwrap_or_else(|e| {
    eprintln!("{e}");
    std::process::exit(1);
  })
}

fn main() {
  let matches = Command::new("kind2")
    .about("The Kind2 Programming Language")
    .subcommand_required(true)
    .arg_required_else_help(true)
    .subcommand(Command::new("check")
      .about("Type-checks a term")
      .arg(Arg::new("name").required(true))
      .arg(Arg::new("runtime")
        .long("use")
        .value_parser(["hs", "hvm2"])
        .default_value("hs")))
    .subcommand(Command::new("normal")  
      .about("Normalizes a term")
      .arg(Arg::new("name").required(true))
      .arg(Arg::new("level")
        .long("level")
        .short('l')
        .action(ArgAction::Set)
        .value_parser(clap::value_parser!(u32)))
      .arg(Arg::new("runtime")
        .long("use")
        .value_parser(["hs", "hvm2"])
        .default_value("hs")))
    .subcommand(Command::new("format")
      .about("Auto-formats a file")
      .arg(Arg::new("name").required(true)))
    .subcommand(Command::new("compile")
      .about("Compiles to HVM2")  
      .arg(Arg::new("name").required(true)))
    .subcommand(Command::new("compare").about("Runs internal comparison tests"))
    .get_matches();

  match matches.subcommand() {
    Some(("check", sub_matches)) => {
      let name = sub_matches.get_one::<String>("name").expect("required");
      let runtime = sub_matches.get_one::<String>("runtime").expect("defaulted");
      check(name, runtime);
    }
    Some(("normal", sub_matches)) => {
      let name = sub_matches.get_one::<String>("name").expect("required");
      let level = sub_matches.get_one::<u32>("level").copied().unwrap_or(0);
      let runtime = sub_matches.get_one::<String>("runtime").expect("defaulted");
      normal(name, level, runtime);
    }
    Some(("format", sub_matches)) => {
      let name = sub_matches.get_one::<String>("name").expect("required");
      auto_format(name);
    }
    Some(("compile", sub_matches)) => {
      let name = sub_matches.get_one::<String>("name").expect("required");
      compile(name);
    }
    Some(("compare", _)) => compare_runtimes(),
    _ => unreachable!(),
  }
}
