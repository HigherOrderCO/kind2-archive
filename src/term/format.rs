use crate::{*};

impl Oper {

  pub fn format(&self) -> Box<Form> {
    Form::text(self.show())
  }

}

impl Term {

  pub fn format(&self) -> Box<Form> {
    self.clean().format_go()
  }

  pub fn format_go(&self) -> Box<Form> {
    match self {
      Term::All { .. } => {
        let mut bnd = vec![];
        let mut bod = self;
        while let Term::All { nam, inp, bod: in_bod } = bod {
          bnd.push(Form::call("", vec![
            Form::glue("", vec![
              Form::text("∀("),
              Form::text(nam),
              Form::text(": "),
            ]),
            inp.format_go(),
            Form::text(")"),
          ]));
          bod = in_bod;
        }
        Form::pile(" ", vec![
          Form::pile(" ", bnd),
          bod.format_go(),
        ])
      },
      Term::Lam { .. } => {
        let mut bnd = vec![];
        let mut bod = self;
        while let Term::Lam { nam, bod: in_bod } = bod {
          bnd.push(Form::text(&format!("λ{}",nam)));
          bod = in_bod;
        }
        Form::pile(" ", vec![
          Form::glue(" ", bnd),
          bod.format_go(),
        ])
      },
      Term::App { .. } => {
        let mut fun = self;
        let mut spn = vec![];
        while let Term::App { fun: in_fun, arg } = fun {
          spn.push(arg);
          fun = in_fun;
        }
        let mut vec = vec![];
        vec.push(Form::glue("", vec![
          Form::text("("),
          fun.format_go(),
        ]));
        spn.reverse();
        for arg in spn {
          vec.push(arg.format_go());
        }
        vec.push(Form::text(")"));
        Form::call(" ", vec)
      }
      Term::Ann { chk: _, val, typ } => {
        Form::call("", vec![
          Form::glue("", vec![
            Form::text("{"),
            val.format_go(),
          ]),
          Form::glue("", vec![
            Form::text(":"),
            typ.format_go(),
            Form::text("}"),
          ])
        ])
      },
      Term::Slf { nam, typ, bod } => {
        Form::pile(" ", vec![
          Form::glue("", vec![
            Form::text("$("),
            Form::text(nam),
            Form::text(": "),
            typ.format_go(),
            Form::text(")"),
          ]),
          bod.format_go(),
        ])
      }
      Term::Ins { val } => {
        Form::glue("", vec![
          Form::text("~"),
          val.format_go(),
        ])
      },
      Term::Set => {
        Form::text("*")
      },
      Term::U60 => {
        Form::text("#U60")
      },
      Term::Num { val } => {
        Form::text(&format!("#{}", val))
      },
      Term::Op2 { opr, fst, snd } => {
        Form::call(" ", vec![
          Form::glue("", vec![
            Form::text("#("),
            opr.format(),
          ]),
          Form::glue("", vec![
            fst.format_go(),
          ]),
          Form::glue("", vec![
            snd.format_go(),
          ]),
          Form::text(")"),
        ])
      },
      Term::Mat { nam, x, z, s, p } => {
        Form::call(" ", vec![
          Form::glue(" ", vec![
            Form::text("#match"),
            Form::text(nam),
            Form::text("="),
            x.format_go(),
            Form::text("{"),
          ]),
          Form::glue("", vec![
            Form::text("#0: "),
            z.format_go(),
          ]),
          Form::glue("", vec![
            Form::text("#+: "),
            s.format_go(),
            Form::text(" "),
          ]),
          Form::glue("", vec![
            Form::text("}: "),
            p.format_go(),
          ]),
        ])
      },
      Term::Txt { txt } => {
        Form::text(&format!("\"{}\"", txt))
      },
      Term::Let { nam, val, bod } => {
        Form::glue("", vec![
          Form::text("let "),
          Form::text(nam),
          Form::text(" = "),
          Form::inc(),
          val.format_go(),
          Form::dec(),
          Form::line(),
          bod.format_go(),
        ])
      },
      Term::Use { nam, val, bod } => {
        Form::glue("", vec![
          Form::text("use "),
          Form::text(nam),
          Form::text(" = "),
          Form::inc(),
          val.format_go(),
          Form::dec(),
          Form::line(),
          bod.format_go(),
        ])
      },
      Term::Hol { nam } => {
        Form::text(&format!("?{}", nam))
      },
      Term::Met {} => {
        Form::text("_")
      },
      Term::Var { nam } => {
        Form::text(nam)
      },
      Term::Src { src: _, val } => {
        val.format_go()
      },
    }
  }

}
