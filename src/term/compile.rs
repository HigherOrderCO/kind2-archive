use crate::{*};

impl Oper {
  pub fn to_ctr(&self) -> &'static str {
    match self {
      Oper::Add => "ADD",
      Oper::Sub => "SUB",
      Oper::Mul => "MUL",
      Oper::Div => "DIV",
      Oper::Mod => "MOD",
      Oper::Eq  => "EQ",
      Oper::Ne  => "NE",
      Oper::Lt  => "LT",
      Oper::Gt  => "GT",
      Oper::Lte => "LTE",
      Oper::Gte => "GTE",
      Oper::And => "AND",
      Oper::Or  => "OR",
      Oper::Xor => "XOR",
      Oper::Lsh => "LSH",
      Oper::Rsh => "RSH",
    }
  }

  pub fn to_sym(&self) -> &'static str {
    match self {
      Oper::Add => "+",
      Oper::Sub => "-",
      Oper::Mul => "*",
      Oper::Div => "/",
      Oper::Mod => "%",
      Oper::Eq  => "==",
      Oper::Ne  => "!=",
      Oper::Lt  => "<",
      Oper::Gt  => ">",
      Oper::Lte => "<=",
      Oper::Gte => ">=",
      Oper::And => "&&",
      Oper::Or  => "||",
      Oper::Xor => "^",
      Oper::Lsh => "<<",
      Oper::Rsh => ">>",
    }
  }
}

impl Term {
  pub fn to_hvm2(&self) -> String {
    match self {
      Term::All { era: _, nam: _, inp: _, bod: _ } => {
        format!("0")
      },
      Term::Lam { era, nam, bod } => {
        let bod = bod.to_hvm2();
        if *era {
          format!("{}", bod)
        } else {
          format!("λ{} {}", Term::to_hvm2_name(nam), bod)
        }
      },
      Term::App { era, fun, arg } => {
        if *era {
          let fun = fun.to_hvm2();
          format!("{}", fun)
        } else {
          let fun = fun.to_hvm2();
          let arg = arg.to_hvm2();
          format!("({} {})", fun, arg)
        }
      },
      Term::Ann { chk: _, val, typ: _ } => {
        val.to_hvm2()
      },
      Term::Slf { nam: _, typ: _, bod: _ } => {
        format!("0")
      },
      Term::Ins { val } => {
        val.to_hvm2()
      },
      Term::Set => {
        format!("0")
      },
      Term::U60 => {
        format!("0")
      },
      Term::Num { val } => {
        format!("{}", val)
      },
      Term::Op2 { opr, fst, snd } => {
        let fst = fst.to_hvm2();
        let snd = snd.to_hvm2();
        format!("({} {} {})", opr.to_sym(), fst, snd)
      },
      Term::Swi { nam, x, z, s, p: _ } => {
        let x = x.to_hvm2();
        let z = z.to_hvm2();
        let s = s.to_hvm2();
        format!("match {} = {} {{ 0: {} 1+: {} }}", Term::to_hvm2_name(nam), x, z, s)
      },
      Term::Let { nam, val, bod } => {
        let val = val.to_hvm2();
        let bod = bod.to_hvm2();
        format!("let {} = {} {}", Term::to_hvm2_name(nam), val, bod)
      },
      // FIXME: change to "use" once hvm-lang supports it
      Term::Use { nam, val, bod } => {
        let val = val.to_hvm2();
        let bod = bod.to_hvm2();
        format!("let {} = {} {}", Term::to_hvm2_name(nam), val, bod)
      },
      Term::Hol { nam: _ } => {
        format!("0")
      },
      Term::Met {} => { 
        println!("WARNING: unsolved metas.");
        format!("0")
      },
      Term::Var { nam } => {
        format!("{}", Term::to_hvm2_name(nam)) 
      },
      Term::Src { src: _, val } => {
        val.to_hvm2()
      },
      Term::Nat { nat } => {
        format!("#{}", nat)
      },
      Term::Txt { txt } => {
        format!("\"{}\"", txt.replace("\n", "\\n"))
      },
      Term::Mch { .. } => {
        unreachable!()
      },
    }
  }

  pub fn to_hvm2_name(name: &str) -> String {
    format!("_{}", name.replace("/","."))
  }
}

impl Term {
  pub fn to_kindc(&self, met: &mut usize) -> String {
    match self {
      Term::All { era: _, nam, inp, bod } => {
        format!("∀({}: {}) {}", nam, inp.to_kindc(met), bod.to_kindc(met))
      },
      Term::Lam { era: _, nam, bod } => {
        format!("λ{} {}", nam, bod.to_kindc(met))
      },
      Term::App { era: _, fun, arg } => {
        format!("({} {})", fun.to_kindc(met), arg.to_kindc(met))
      },
      Term::Ann { chk, val, typ } => {
        format!("{{{}:{} {}}}", val.to_kindc(met), if *chk { ":" } else { "" }, typ.to_kindc(met))
      },
      Term::Slf { nam, typ, bod } => {
        format!("$({}: {}) {}", nam, typ.to_kindc(met), bod.to_kindc(met))
      },
      Term::Ins { val } => {
        format!("~{}", val.to_kindc(met))
      },
      Term::Set => "*".to_string(),
      Term::U60 => "U60".to_string(),
      Term::Num { val } => val.to_string(),
      Term::Op2 { opr, fst, snd } => {
        format!("({} {} {})", opr.to_kindc(), fst.to_kindc(met), snd.to_kindc(met))
      },
      Term::Swi { nam, x, z, s, p } => {
        format!("switch {} = {} {{ 0: {} _: {} }}: {}", nam, x.to_kindc(met), z.to_kindc(met), s.to_kindc(met), p.to_kindc(met))
      },
      Term::Let { nam, val, bod } => {
        format!("let {} = {}; {}", nam, val.to_kindc(met), bod.to_kindc(met))
      },
      Term::Use { nam, val, bod } => {
        format!("use {} = {}; {}", nam, val.to_kindc(met), bod.to_kindc(met))
      },
      Term::Hol { nam } => format!("?{}", nam),
      Term::Met { .. } => {
        let uid = *met;
        *met += 1;
        format!("_{}", uid)
      },
      Term::Var { nam } => nam.clone(),
      Term::Src { src, val } => format!("!{} {}", src.to_u64(), val.to_kindc(met)),
      Term::Nat { nat } => format!("#{}", nat),
      Term::Txt { txt } => format!("\"{}\"", txt.replace("\n", "\\n")),
      Term::Mch { .. } => unreachable!(),
    }
  }

  pub fn to_kindc_name(name: &str) -> String {
    name.to_string()
  }
}

impl Oper {
  pub fn to_kindc(&self) -> &'static str {
    match self {
      Oper::Add => "+",
      Oper::Sub => "-",
      Oper::Mul => "*",
      Oper::Div => "/",
      Oper::Mod => "%",
      Oper::Eq  => "==",
      Oper::Ne  => "!=",
      Oper::Lt  => "<",
      Oper::Gt  => ">",
      Oper::Lte => "<=",
      Oper::Gte => ">=",
      Oper::And => "&",
      Oper::Or  => "|",
      Oper::Xor => "^",
      Oper::Lsh => "<<",
      Oper::Rsh => ">>",
    }
  }
}
