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

  pub fn to_hvm1_checker(&self) -> &'static str {
    self.to_ctr()
  }

  pub fn to_hs_checker(&self) -> &'static str {
    self.to_ctr()
  }

}

impl Term {

  pub fn to_hvm1_checker(&self, _env: im::Vector<String>, _met: &mut usize) -> String {
    todo!()
  }
  
  pub fn to_hs_name(name: &str) -> String {
    format!("x{}", name.replace("-", "_").replace(".","_"))
  }

  pub fn to_hs_checker(&self, env: im::Vector<String>, met: &mut usize) -> String {
    match self {
      Term::All { nam, inp, bod } => {
        let inp = inp.to_hs_checker(env.clone(), met);
        let bod = bod.to_hs_checker(cons(&env, nam.clone()), met);
        format!("(All \"{}\" {} $ \\{} -> {})", nam, inp, Term::to_hs_name(nam), bod)
      },
      Term::Lam { nam, bod } => {
        let bod = bod.to_hs_checker(cons(&env, nam.clone()), met);
        format!("(Lam \"{}\" $ \\{} -> {})", nam, Term::to_hs_name(nam), bod)
      },
      Term::App { fun, arg } => {
        let fun = fun.to_hs_checker(env.clone(), met);
        let arg = arg.to_hs_checker(env.clone(), met);
        format!("(App {} {})", fun, arg)
      },
      Term::Ann { chk, val, typ } => {
        let val = val.to_hs_checker(env.clone(), met);
        let typ = typ.to_hs_checker(env.clone(), met);
        format!("(Ann {} {} {})", if *chk { "True" } else { "False" }, val, typ)
      },
      Term::Slf { nam, typ, bod } => {
        let typ = typ.to_hs_checker(env.clone(), met);
        let bod = bod.to_hs_checker(cons(&env, nam.clone()), met);
        format!("(Slf \"{}\" {} $ \\{} -> {})", nam, typ, Term::to_hs_name(nam), bod)
      },
      Term::Ins { val } => {
        let val = val.to_hs_checker(env.clone(), met);
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
        let fst = fst.to_hs_checker(env.clone(), met);
        let snd = snd.to_hs_checker(env.clone(), met);
        format!("(Op2 {} {} {})", opr.to_hs_checker(), fst, snd)
      },
      Term::Swi { nam, x, z, s, p } => {
        let x = x.to_hs_checker(env.clone(), met);
        let z = z.to_hs_checker(env.clone(), met);
        let s = s.to_hs_checker(cons(&env, format!("{}-1", nam)), met);
        let p = p.to_hs_checker(cons(&env, nam.clone()), met);
        format!("(Swi \"{}\" {} {} (\\{} -> {}) (\\{} -> {}))", nam, x, z, Term::to_hs_name(&format!("{}-1", nam)), s, Term::to_hs_name(nam), p)
      },
      Term::Let { nam, val, bod } => {
        let val = val.to_hs_checker(env.clone(), met);
        let bod = bod.to_hs_checker(cons(&env, nam.clone()), met);
        format!("(Let \"{}\" {} $ \\{} -> {})", nam, val, Term::to_hs_name(nam), bod)
      },
      Term::Use { nam, val, bod } => {
        let val = val.to_hs_checker(env.clone(), met);
        let bod = bod.to_hs_checker(cons(&env, nam.clone()), met);
        format!("(Use \"{}\" {} $ \\{} -> {})", nam, val, Term::to_hs_name(nam), bod)
      },
      Term::Hol { nam } => {
        let env_str = env.iter().map(|n| Term::to_hs_name(n)).collect::<Vec<_>>().join(",");
        format!("(Hol \"{}\" [{}])", nam, env_str)
      },
      Term::Met {} => { 
        let uid = *met; 
        *met += 1; 
        format!("(Met {} [])", uid)
        //format!("(Met {} [{}])", uid, env.iter().rev().map(|n| Term::to_hs_name(n)).collect::<Vec<_>>().join(","))
      },
      Term::Var { nam } => {
        format!("{}", Term::to_hs_name(nam)) 
      },
      Term::Src { src, val } => {
        let val = val.to_hs_checker(env, met);
        format!("(Src {} {})", src.to_u64(), val)
      },
      Term::Nat { nat } => {
        format!("(Nat {})", nat)
      },
      Term::Txt { txt } => {
        format!("(Txt \"{}\")", txt.replace("\n", "\\n"))
      },
      Term::Mch { .. } => {
        unreachable!()
      },
    }
  }



}
