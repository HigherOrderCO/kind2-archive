use crate::{*};

impl Oper {

  pub fn to_hvm1(&self) -> &'static str {
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

}

impl Term {

  pub fn to_hvm1(&self, env: im::Vector<String>, met: &mut usize) -> String {
    fn binder(name: &str) -> String {
      format!("x{}", name.replace("-", "._."))
    }
    match self {
      Term::All { nam, inp, bod } => {
        let inp = inp.to_hvm1(env.clone(), met);
        let bod = bod.to_hvm1(cons(&env, nam.clone()), met);
        format!("(All \"{}\" {} λ{} {})", nam, inp, binder(nam), bod)
      },
      Term::Lam { nam, bod } => {
        let bod = bod.to_hvm1(cons(&env, nam.clone()), met);
        format!("(Lam \"{}\" λ{} {})", nam, binder(nam), bod)
      },
      Term::App { fun, arg } => {
        let fun = fun.to_hvm1(env.clone(), met);
        let arg = arg.to_hvm1(env.clone(), met);
        format!("(App {} {})", fun, arg)
      },
      Term::Ann { val, typ } => {
        let val = val.to_hvm1(env.clone(), met);
        let typ = typ.to_hvm1(env.clone(), met);
        format!("(Ann {} {})", val, typ)
      },
      Term::Slf { nam, typ, bod } => {
        let typ = typ.to_hvm1(env.clone(), met);
        let bod = bod.to_hvm1(cons(&env, nam.clone()), met);
        format!("(Slf \"{}\" {} λ{} {})", nam, typ, binder(nam), bod)
      },
      Term::Ins { val } => {
        let val = val.to_hvm1(env.clone(), met);
        format!("(Ins {})", val)
      },
      Term::Set => {
        "(Set)".to_string()
      },
      Term::U60 => {
        "(U60)".to_string()
      },
      Term::Num { val } => {
        format!("(Num {})", val)
      },
      Term::Op2 { opr, fst, snd } => {
        let fst = fst.to_hvm1(env.clone(), met);
        let snd = snd.to_hvm1(env.clone(), met);
        format!("(Op2 {} {} {})", opr.to_hvm1(), fst, snd)
      },
      Term::Mat { nam, x, z, s, p } => {
        let x = x.to_hvm1(env.clone(), met);
        let z = z.to_hvm1(env.clone(), met);
        let s = s.to_hvm1(cons(&env, format!("{}-1", nam)), met);
        let p = p.to_hvm1(cons(&env, nam.clone()), met);
        format!("(Mat \"{}\" {} {} λ{} {} λ{} {})", nam, x, z, binder(&format!("{}-1", nam)), s, binder(nam), p)
      },
      Term::Txt { txt } => {
        format!("(Txt \"{}\")", txt)
      },
      Term::Let { nam, val, bod } => {
        let val = val.to_hvm1(env.clone(), met);
        let bod = bod.to_hvm1(cons(&env, nam.clone()), met);
        format!("(Let \"{}\" {} λ{} {})", nam, val, binder(nam), bod)
      },
      Term::Hol { nam } => {
        let env_str = env.iter().map(|n| binder(n)).collect::<Vec<_>>().join(",");
        format!("(Hol \"{}\" [{}])", nam, env_str)
      },
      Term::Met {} => { 
        let n = *met; 
        *met += 1; 
        format!("(Met \"{}\" {})", n, format!("_{}", n)) 
      },
      Term::Var { nam } => {
        if env.contains(nam) { 
          format!("{}", binder(nam)) 
        } else { 
          format!("(Book.{})", nam) 
        }
      },
      Term::Src { src, val } => {
        let val = val.to_hvm1(env, met);
        format!("(Src {} {})", src.to_u64(), val)
      },
    }
  }

}
