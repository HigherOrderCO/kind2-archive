//./../sugar/mod.rs//

use std::fmt::Display;

use crate::{*};

impl Oper {
  pub fn show(&self) -> String {
    self.to_string()
  }
}

impl Term {
  pub fn show(&self) -> String {
    self.to_string()
  }
}

impl Display for Oper {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(
      f,
      "{}",
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
    )
  }
}

impl Display for Term {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if let Some(nat) = self.as_nat() {
      return write!(f, "{nat}");
    }

    if let Some(list) = self.as_list() {
      return write!(f, "{list}");
    }

    if let Some(equal) = self.as_equal() {
      return write!(f, "{equal}");
    }

    if let Some(adt) = self.as_adt() {
      return write!(f, "{adt}");
    }

    match self {
      Term::All { .. } => {
        let mut bod = self;
        while let Term::All { era: _, nam, inp, bod: in_bod } = bod {
          write!(f, "∀({nam}: {inp}) ")?;
          bod = in_bod;
        }

        write!(f, "{bod}")
      }

      Term::Lam { .. } => {
        let mut bod = self;
        while let Term::Lam { era: _, nam, bod: in_bod } = bod {
          write!(f, "λ{nam} ")?;
          bod = in_bod;
        }

        write!(f, "{bod}")
      }

      Term::App { .. } => {
        let mut fun = self;
        let mut args = vec![];
        while let Term::App { era: _, fun: in_fun, arg } = fun {
          args.push(arg.to_string());
          fun = in_fun;
        }
        args.reverse();

        write!(f, "({fun} {})", args.join(" "))
      }

      Term::Ann { chk: _, val, typ: _ } => write!(f, "{val}"),
      Term::Slf { nam, typ, bod } => write!(f, "$({nam}: {typ}) {bod}"),
      Term::Ins { val } => write!(f, "~{val}"),
      Term::Set => write!(f, "*"),
      Term::U48 => write!(f, "U60"),
      Term::Num { val } => write!(f, "{val}"),
      Term::Op2 { opr, fst, snd } => write!(f, "({opr} {fst} {snd})"),
      Term::Swi { nam, x, z, s, p } => write!(f, "switch {nam} = {x} {{0: {z} _: {s}}}: {p}"),
      Term::Let { nam, val, bod } => write!(f, "let {nam} = {val}; {bod}"),
      Term::Use { nam, val, bod } => write!(f, "use {nam} = {val}; {bod}"),
      Term::Hol { nam } => write!(f, "?{nam}"),
      Term::Met {} => write!(f, "_"),
      Term::Var { nam } => write!(f, "{nam}"),
      Term::Src { src: _, val } => write!(f, "{val}"),
      Term::Txt { txt } => write!(f, "\"{txt}\""),
      Term::Nat { nat } => write!(f, "{nat}"),
      Term::Mch { mch } => write!(f, "{mch}"),
    }
  }
}
