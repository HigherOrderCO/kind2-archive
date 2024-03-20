use crate::{*};

impl Book {

  pub fn to_hvm1_checker(&self) -> String {
    todo!()
    //let mut used = BTreeSet::new();
    //let mut code = String::new();
    //for (name, term) in &self.defs {
      //let metas = term.count_metas();
      //let mut lams = String::new();
      //for i in 0 .. term.count_metas() {
        //lams = format!("{} λ_{}", lams, i);
      //}
      //let subs = (0 .. metas).map(|h| format!("(Pair \"{}\" None)", h)).collect::<Vec<_>>().join(",");
      //code.push_str(&format!("Book.{} = (Ref \"{}\" [{}] {}{})\n", name, name, subs, lams, term.to_hvm1(im::Vector::new(), &mut 0)));
      //used.insert(name.clone());
    //}
    //code
  }

  pub fn to_hvm2_checker(&self) -> String {
    let mut code = String::new();
    let mut meta = 0;
    for (name, term) in &self.defs {
      let expr = term.to_hvm2_checker(im::Vector::new(), &mut meta);
      code.push_str(&format!("Book.{} = (Ref \"{}\" {})\n", name.replace("/", "."), name, expr));
    }
    code
  }

  pub fn to_hs_checker(&self) -> String {
    let mut code = String::new();
    let mut meta = 0;
    for (name, term) in &self.defs {
      let expr = term.to_hs_checker(im::Vector::new(), &mut meta);
      code.push_str(&format!("{} = (Ref \"{}\" {})\n", Term::to_hs_name(name), name, expr));
    }
    code
  }

  pub fn to_hvm2(&self) -> String {
    let mut code = String::new();
    for (name, term) in &self.defs {
      code.push_str(&format!("{} = {}\n", Term::to_hvm2_name(name), term.to_hvm2()));
    }
    code
  }

}
