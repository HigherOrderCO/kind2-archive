use crate::{*};

// Kind -> HVM2
// ------------

impl Oper {
  pub fn to_hvm2(&self) -> &'static str {
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
      Term::U48 => {
        format!("0")
      },
      Term::Num { val } => {
        format!("{}", val)
      },
      Term::Op2 { opr, fst, snd } => {
        let fst = fst.to_hvm2();
        let snd = snd.to_hvm2();
        format!("({} {} {})", opr.to_hvm2(), fst, snd)
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

// Kind -> KindCore
// ----------------

impl Term {
  pub fn to_kindc(&self, env: im::Vector<String>, met: &mut usize) -> String {
    match self {
      Term::All { era: _, nam, inp, bod } => {
        format!("∀({}: {}) {}", nam, inp.to_kindc(env.clone(), met), bod.to_kindc(cons(&env, nam.clone()), met))
      },
      Term::Lam { era: _, nam, bod } => {
        format!("λ{} {}", nam, bod.to_kindc(cons(&env, nam.clone()), met))
      },
      Term::App { era: _, fun, arg } => {
        format!("({} {})", fun.to_kindc(env.clone(), met), arg.to_kindc(env.clone(), met))
      },
      Term::Ann { chk, val, typ } => {
        format!("{{{}:{} {}}}", val.to_kindc(env.clone(), met), if *chk { ":" } else { "" }, typ.to_kindc(env.clone(), met))
      },
      Term::Slf { nam, typ, bod } => {
        format!("$({}: {}) {}", nam, typ.to_kindc(env.clone(), met), bod.to_kindc(cons(&env, nam.clone()), met))
      },
      Term::Ins { val } => {
        format!("~{}", val.to_kindc(env.clone(), met))
      },
      Term::Set => "*".to_string(),
      Term::U48 => "U48".to_string(),
      Term::Num { val } => val.to_string(),
      Term::Op2 { opr, fst, snd } => {
        format!("({} {} {})", opr.to_kindc(), fst.to_kindc(env.clone(), met), snd.to_kindc(env.clone(), met))
      },
      Term::Swi { nam, x, z, s, p } => {
        format!("switch {} = {} {{ 0: {} _: {} }}: {}", nam, x.to_kindc(env.clone(), met), z.to_kindc(env.clone(), met), s.to_kindc(cons(&env, format!("{}-1", nam)), met), p.to_kindc(cons(&env, nam.clone()), met))
      },
      Term::Let { nam, val, bod } => {
        format!("let {} = {}; {}", nam, val.to_kindc(env.clone(), met), bod.to_kindc(cons(&env, nam.clone()), met))
      },
      Term::Use { nam, val, bod } => {
        format!("use {} = {}; {}", nam, val.to_kindc(env.clone(), met), bod.to_kindc(cons(&env, nam.clone()), met))
      },
      Term::Hol { nam } => {
        let env_str = env.iter().map(|n| Term::to_kindc_name(n)).collect::<Vec<_>>().join(",");
        format!("?{}[{}]", nam, env_str)
      },
      Term::Met { .. } => {
        let uid = *met;
        *met += 1;
        format!("_{}", uid)
      },
      Term::Var { nam } => Term::to_kindc_name(nam),
      Term::Src { src, val } => format!("!{} {}", src.to_u64(), val.to_kindc(env, met)),
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

// Kind -> JavaScript
// ------------------

impl Term {

  pub fn to_js(&self) -> String {
    let mut term = self.clone();
    //println!("OVERSHADOW:");
    //println!("{}", term.show());
    term.overshadow(&im::HashMap::new(), &mut 0);
    //println!("{}", term.show());
    //term.desugar();
    //term.expand_implicits(im::Vector::new(), &BTreeMap::new());
    term.to_js_go()
  }
  
  pub fn to_js_go(&self) -> String {
    match self {
      Term::All { era: _, nam: _, inp: _, bod: _ } => {
        "null".to_string()
      },
      Term::Lam { era: _, nam, bod } => {
        format!("({}) => {}", Term::to_js_name(nam), bod.to_js_go())
      },
      Term::App { era: _, fun, arg } => {
        format!("{}({})", fun.to_js_go(), arg.to_js_go())
      },
      Term::Ann { chk: _, val, typ: _ } => {
        val.to_js_go()
      },
      Term::Slf { nam: _, typ: _, bod: _ } => {
        "null".to_string()
      },
      Term::Ins { val } => {
        val.to_js_go()
      },
      Term::Set => {
        "null".to_string()
      },
      Term::U48 => {
        "null".to_string()
      },
      Term::Num { val } => {
        val.to_string()
      },
      Term::Op2 { opr, fst, snd } => {
        format!("Math.floor({} {} {})", fst.to_js_go(), opr.to_js(), snd.to_js_go())
      },
      Term::Swi { nam, x, z, s, p: _ } => {
        format!("(() => {{ const {} = {}; switch ({}) {{ case 0: return {}; default: return (({} => {})(({}) - 1)); }} }})()",
          Term::to_js_name(nam), x.to_js_go(), Term::to_js_name(nam), z.to_js_go(), Term::to_js_name(nam), s.to_js_go(), Term::to_js_name(nam))
      },
      Term::Let { nam, val, bod } => {
        format!("(() => {{ const {} = {}; return {}; }})()", Term::to_js_name(nam), val.to_js_go(), bod.to_js_go())
      },
      Term::Use { nam, val, bod } => {
        format!("(() => {{ const {} = {}; return {}; }})()", Term::to_js_name(nam), val.to_js_go(), bod.to_js_go())
      },
      Term::Hol { nam: _ } => {
        "null".to_string()
      },
      Term::Met {} => {
        //println!("WARNING: unsolved metas.");
        "null".to_string()
      },
      Term::Var { nam } => {
        Term::to_js_name(nam)
      },
      Term::Src { src: _, val } => {
        val.to_js_go()
      },
      Term::Nat { nat } => {
        format!("{}", nat)
      },
      Term::Txt { txt } => {
        format!("\"{}\"", txt.replace("\n", "\\n"))
      },
      Term::Mch { .. } => {
        unreachable!()
      },
    }
  }

  pub fn to_js_name(name: &str) -> String {
    name.replace("/", "_").replace(".","_").replace("-","_")
  }
}

impl Oper {
  pub fn to_js(&self) -> &'static str {
    match self {
      Oper::Add => "+",
      Oper::Sub => "-",
      Oper::Mul => "*",
      Oper::Div => "/",
      Oper::Mod => "%",
      Oper::Eq  => "===",
      Oper::Ne  => "!==",
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


