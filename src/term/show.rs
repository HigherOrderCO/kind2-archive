//./../sugar/mod.rs//

use crate::{*};

impl Oper {

  pub fn show(&self) -> String {
    return self.format().flatten(None);
  }

  pub fn format(&self) -> Box<Show> {
    Show::text(match self {
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
    })
  }

}

impl Term {

  pub fn show(&self) -> String {
    return self.format().flatten(None);
  }

  pub fn format(&self) -> Box<Show> {
    return self.clean().format_go();
  }

  pub fn format_go(&self) -> Box<Show> {

    // Shows a Nat
    if let Some(nat) = self.as_nat() {
      return Show::text(&format!("{}", nat));
    }

    // Shows a List
    if let Some(list) = self.as_list() {
      return list.format();
    }

    // Shows an Equal
    if let Some(equal) = self.as_equal() {
      return equal.format();
    }

    // Shows an ADT
    if let Some(adt) = self.as_adt() {
      return adt.format();
    }

    match self {
      Term::All { .. } => {
        let mut bnd = vec![];
        let mut bod = self;
        while let Term::All { era: _, nam, inp, bod: in_bod } = bod {
          bnd.push(Show::call("", vec![
            Show::glue("", vec![
              Show::text("∀("),
              Show::text(nam),
              Show::text(": "),
            ]),
            inp.format_go(),
            Show::text(")"),
          ]));
          bod = in_bod;
        }
        Show::pile(" ", vec![
          Show::pile(" ", bnd),
          bod.format_go(),
        ])
      },
      Term::Lam { .. } => {
        let mut bnd = vec![];
        let mut bod = self;
        while let Term::Lam { era: _, nam, bod: in_bod } = bod {
          bnd.push(Show::text(&format!("λ{}",nam)));
          bod = in_bod;
        }
        Show::pile(" ", vec![
          Show::glue(" ", bnd),
          bod.format_go(),
        ])
      },
      Term::App { .. } => {
        let mut fun = self;
        let mut spn = vec![];
        while let Term::App { era: _, fun: in_fun, arg } = fun {
          spn.push(arg);
          fun = in_fun;
        }
        let mut vec = vec![];
        vec.push(Show::glue("", vec![
          Show::text("("),
          fun.format_go(),
        ]));
        spn.reverse();
        for arg in spn {
          vec.push(arg.format_go());
        }
        vec.push(Show::text(")"));
        Show::call(" ", vec)
      }
      Term::Ann { chk: _, val, typ: _ } => {
        val.format_go()
        //Show::call(" ", vec![
          //val.format_go(),
          //Show::text("::"),
          //typ.format_go(),
        //])
      },
      Term::Slf { nam, typ, bod } => {
        Show::pile(" ", vec![
          Show::glue("", vec![
            Show::text("$("),
            Show::text(nam),
            Show::text(": "),
            typ.format_go(),
            Show::text(")"),
          ]),
          bod.format_go(),
        ])
      }
      Term::Ins { val } => {
        Show::glue("", vec![
          Show::text("~"),
          val.format_go(),
        ])
      },
      Term::Set => {
        Show::text("*")
      },
      Term::U48 => {
        Show::text("U48")
      },
      Term::Num { val } => {
        Show::text(&format!("{}", val))
      },
      Term::Op2 { opr, fst, snd } => {
        Show::call(" ", vec![
          Show::glue("", vec![
            Show::text("("),
            opr.format(),
          ]),
          Show::glue("", vec![
            fst.format_go(),
          ]),
          Show::glue("", vec![
            snd.format_go(),
          ]),
          Show::text(")"),
        ])
      },
      Term::Swi { nam, x, z, s, p } => {
        Show::call(" ", vec![
          Show::glue(" ", vec![
            Show::text("switch"),
            Show::text(nam),
            Show::text("="),
            x.format_go(),
            Show::text("{"),
          ]),
          Show::glue("", vec![
            Show::text("0: "),
            z.format_go(),
          ]),
          Show::glue("", vec![
            Show::text("_: "),
            s.format_go(),
            Show::text(" "),
          ]),
          Show::glue("", vec![
            Show::text("}: "),
            p.format_go(),
          ]),
        ])
      },
      Term::Let { nam, val, bod } => {
        Show::glue("", vec![
          Show::text("let "),
          Show::text(nam),
          Show::text(" = "),
          Show::inc(),
          val.format_go(),
          Show::dec(),
          Show::semi(),
          bod.format_go(),
        ])
      },
      Term::Use { nam, val, bod } => {
        Show::glue("", vec![
          Show::text("use "),
          Show::text(nam),
          Show::text(" = "),
          Show::inc(),
          val.format_go(),
          Show::dec(),
          Show::semi(),
          bod.format_go(),
        ])
      },
      Term::Hol { nam } => {
        Show::text(&format!("?{}", nam))
      },
      Term::Met {} => {
        Show::text("_")
      },
      Term::Var { nam } => {
        Show::text(nam)
      },
      Term::Src { src: _, val } => {
        val.format_go()
      },
      Term::Txt { txt } => {
        Show::text(&format!("\"{}\"", txt))
      },
      Term::Nat { nat } => {
        Show::text(&format!("{}", nat))
      },
      Term::Mch { mch: _ } => {
        // FIXME: isn't this unreachable?
        unreachable!()
        //Show::call(" ", vec![
          //Show::glue(" ", vec![
            //Show::text("match"),
            //Show::text(&mch.name),
            //if let Some(expr) = &mch.expr {
              //Show::glue(" ", vec![
                //Show::text("="),
                //expr.format_go(),
              //])
            //} else {
              //Show::text("")
            //},
            //if !mch.with.is_empty() {
              //Show::glue(" ", vec![
                //Show::text("with"),
                //Show::pile(" ", mch.with.iter().map(|(name, typ)| {
                  //Show::call("", vec![
                    //Show::text("("),
                    //Show::text(name),
                    //Show::text(":"),
                    //typ.format_go(),
                    //Show::text(")"),
                  //])
                //}).collect()),
              //])
            //} else {
              //Show::text("")
            //},
            //Show::text("{"),
          //]),
          //Show::pile("; ", mch.cses.iter().map(|(nam, bod)| {
            //Show::glue("", vec![
              //Show::text(nam),
              //Show::text(": "),
              //bod.format_go(),
            //])
          //}).collect()),
          //Show::glue("", vec![
            //Show::text("}"),
          //]),
          //mch.moti.as_ref().map_or(
            //Show::text(""),
            //|bod| Show::glue("", vec![
              //Show::text(": "),
              //bod.format_go(),
            //])  
          //),
        //])
      },
    }
  }

}
