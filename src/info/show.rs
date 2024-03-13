use crate::{*};

impl Info {

  pub fn show(&self) -> String {
    match self {
      Info::Found { nam, typ, ctx } => {
        let ctx = ctx.iter().map(|x| x.show()).collect::<Vec<_>>().join(" ");
        format!("#found{{?{} {} [{}]}}", nam, typ.show(), ctx)
      },
      Info::Error { exp, det, bad, src } => {
        format!("#error{{{} {} {} {}}}", exp.show(), det.show(), bad.show(), src.to_u64())
      },
      Info::Solve { nam, val } => {
        format!("#solve{{_{} {}}}", nam, val.show())
      },
      Info::Vague { nam } => {
        format!("#vague{{?{}}}", nam)
      },
      Info::Print { val } => {
        format!("#print{{{}}}", val.show())
      }
    }
  }

}
