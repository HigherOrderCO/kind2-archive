use crate::{*};

mod parse;
mod show;

// <info> ::=
//   FOUND | #found{?<name> <term>}
//   ERROR | #error{<term> <term> <term> <uint>}
//   SOLVE | #solve{_<name> <term>}
//   VAGUE | #vague{_<name>}
#[derive(Clone, Debug)]
pub enum Info {
  Found {
    nam: String,
    typ: Term,
    ctx: Vec<Term>,
  },
  Error {
    exp: Term,
    det: Term,
    bad: Term,
    src: Src,
  },
  Solve {
    nam: String,
    val: Term,
  },
  Vague {
    nam: String,
  },
  Print {
    val: Term,
  },
}


impl Info {

  pub fn pretty(&self, book: &Book) -> String {
    match self {
      Info::Found { nam, typ, ctx } => {
        let msg = format!("?{} :: {}", nam, typ.show());
        let mut ctx_str = String::new();
        for x in ctx.iter() {
          if let Term::Ann { chk: _, val, typ } = x.clean() {
            ctx_str.push_str(&format!("\n- {}: {}", val.show(), typ.show()));
          }
        }
        format!("\x1b[1mFOUND:\x1b[0m {}{}", msg, ctx_str)
      },
      Info::Error { exp, det, bad, src } => {
        let exp  = format!("- expected: \x1b[32m{}\x1b[0m", exp.show());
        let det  = format!("- detected: \x1b[31m{}\x1b[0m", det.show());
        let bad  = format!("- bad_term: \x1b[2m{}\x1b[0m", bad.show());
        let file = book.get_file_name(src.fid).unwrap_or_else(|| "unknown_file".to_string());
        let text = std::fs::read_to_string(&file).unwrap_or_else(|_| "Could not read source file.".to_string());
        let orig = highlight_error(src.ini as usize, src.end as usize, &text);
        let src  = format!("\x1b[4m{}\x1b[0m\n{}", file, orig);
        format!("\x1b[1mERROR:\x1b[0m\n{}\n{}\n{}\n{}", exp, det, bad, src)
      },
      Info::Solve { nam, val } => {
        format!("SOLVE: _{} = {}", nam, val.show())
      },
      Info::Vague { nam } => {
        format!("VAGUE: _{}", nam)
      },
      Info::Print { val } => {
        format!("{}", val.show())
      }
    }
  }

  pub fn parse_infos(input: &str) -> Vec<Info> {
    let mut infos = Vec::new();
    for line in input.lines() {
      let mut parser = KindParser::new(line);
      match parser.parse_info() {
        Ok(info) => infos.push(info),
        Err(_)   => println!(">> {}", line),
      }
    }
    infos
  }

}

