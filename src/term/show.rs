use crate::{*};

impl Oper {

  pub fn show(&self) -> &'static str {
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

impl Term {

  pub fn show(&self) -> String {
    match self {
      Term::All { nam, inp, bod } => {
        let inp = inp.show();
        let bod = bod.show();
        format!("∀({}: {}) {}", nam, inp, bod)
      },
      Term::Lam { nam, bod } => {
        let bod = bod.show();
        format!("λ{} {}", nam, bod)
      },
      Term::App { fun, arg } => {
        let fun = fun.show();
        let arg = arg.show();
        format!("({} {})", fun, arg)
      },
      Term::Ann { val, typ } => {
        let val = val.show();
        let typ = typ.show();
        format!("{{{}: {}}}", val, typ)
      },
      Term::Slf { nam, typ, bod } => {
        let typ = typ.show();
        let bod = bod.show();
        format!("$({}: {}) {}", nam, typ, bod)
      },
      Term::Ins { val } => {
        let val = val.show();
        format!("~{}", val)
      },
      Term::Set => {
        "*".to_string()
      },
      Term::U60 => {
        "#U60".to_string()
      },
      Term::Num { val } => {
        format!("#{}", val)
      },
      Term::Op2 { opr, fst, snd } => {
        let fst = fst.show();
        let snd = snd.show();
        format!("#({} {} {})", opr.show(), fst, snd)
      },
      Term::Mat { nam, x, z, s, p } => {
        let x = x.show();
        let z = z.show();
        let s = s.show();
        let p = p.show();
        format!("#match {} = {} {{ #0: {}; #+: {} }}: {}", nam, x, z, s, p)
      },
      Term::Txt { txt } => {
        format!("\"{}\"", txt)
      },
      Term::Let { nam, val, bod } => {
        let val = val.show();
        let bod = bod.show();
        format!("let {} = {} in {}", nam, val, bod)
      },
      Term::Hol { nam } => {
        format!("?{}", nam)
      },
      Term::Met {} => {
        format!("_")
      },
      Term::Var { nam } => {
        nam.clone()
      },
      Term::Src { src: _, val } => {
        val.show()
      },
    }
  }

}
