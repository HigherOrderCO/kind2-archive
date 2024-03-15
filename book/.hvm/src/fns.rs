use crate::run::{*};

pub const F___main : Val = 0xfbec24b31;
pub const F___foo : Val = 0x3efa9cb2;
pub const F_main : Val = 0xc24b31;
pub const F_a    : Val = 0x000024;
pub const F__U60.fib : Val = 0xf9e180fe9b25;
pub const F_b    : Val = 0x000025;
pub const F_d    : Val = 0x000027;
pub const F_c    : Val = 0x000026;

impl<'a, const LAZY: bool> NetFields<'a, LAZY> where [(); LAZY as usize]: {

  pub fn call_native(&mut self, book: &Book, ptr: Ptr, x: Ptr) -> bool {
    match ptr.val() {
      F___main => { return self.F___main(ptr, Trg::Ptr(x)); }
      F___foo => { return self.F___foo(ptr, Trg::Ptr(x)); }
      F_main => { return self.F_main(ptr, Trg::Ptr(x)); }
      F_a => { return self.F_a(ptr, Trg::Ptr(x)); }
      F__U60.fib => { return self.F__U60.fib(ptr, Trg::Ptr(x)); }
      F_b => { return self.F_b(ptr, Trg::Ptr(x)); }
      F_d => { return self.F_d(ptr, Trg::Ptr(x)); }
      F_c => { return self.F_c(ptr, Trg::Ptr(x)); }
      _ => { return false; }
    }
  }

  pub fn L___main(&mut self, lab: Lab) -> bool {
    if lab == 0x5 { return true; }
    if lab == 0x3 { return true; }
    return false;
  }
  pub fn F___main(&mut self, ptr: Ptr, trg: Trg) -> bool {
    if self.get(trg).is_dup() && !self.L___main(self.get(trg).lab()) {
      self.copy(self.swap(trg, NULL), ptr);
      return true;
    }
    let _k1 : Trg = Trg::Ptr(Ptr::big(REF, F__U60.fib));
    let _k1x : Trg;
    let _k1y : Trg;
    // fast apply
    if self.get(_k1).tag() == LAM {
      self.rwts.anni += 1;
      let got = self.swap(_k1, NULL);
      _k1x = Trg::Dir(Ptr::new(VR1, 0, got.loc()));
      _k1y = Trg::Dir(Ptr::new(VR2, 0, got.loc()));
    } else {
      let k2 = self.alloc();
      _k1x = Trg::Ptr(Ptr::new(VR1, 0, k2));
      _k1y = Trg::Ptr(Ptr::new(VR2, 0, k2));
      self.safe_link(Trg::Ptr(Ptr::new(LAM, 0, k2)), _k1);
    }
    // fast erase
    if self.get(_k1x).is_skp() {
      self.swap(_k1x, NULL);
      self.rwts.eras += 1;
    } else {
      self.safe_link(_k1x, Trg::Ptr(Ptr::new(NUM, 0x6, 0x0)));
    }
    self.safe_link(trg, _k1y);
    return true;
  }

  pub fn L___foo(&mut self, lab: Lab) -> bool {
    return false;
  }
  pub fn F___foo(&mut self, ptr: Ptr, trg: Trg) -> bool {
    if self.get(trg).is_dup() && !self.L___foo(self.get(trg).lab()) {
      self.copy(self.swap(trg, NULL), ptr);
      return true;
    }
    // fast erase
    if self.get(trg).is_skp() {
      self.swap(trg, NULL);
      self.rwts.eras += 1;
    } else {
      self.safe_link(trg, Trg::Ptr(Ptr::new(NUM, 0x2d, 0x0)));
    }
    return true;
  }

  pub fn L_main(&mut self, lab: Lab) -> bool {
    if lab == 0x5 { return true; }
    if lab == 0x3 { return true; }
    return false;
  }
  pub fn F_main(&mut self, ptr: Ptr, trg: Trg) -> bool {
    if self.get(trg).is_dup() && !self.L_main(self.get(trg).lab()) {
      self.copy(self.swap(trg, NULL), ptr);
      return true;
    }
    self.safe_link(trg, Trg::Ptr(Ptr::big(REF, F___main)));
    return true;
  }

  pub fn L_a(&mut self, lab: Lab) -> bool {
    if lab == 0x5 { return true; }
    if lab == 0x3 { return true; }
    return false;
  }
  pub fn F_a(&mut self, ptr: Ptr, trg: Trg) -> bool {
    if self.get(trg).is_dup() && !self.L_a(self.get(trg).lab()) {
      self.copy(self.swap(trg, NULL), ptr);
      return true;
    }
    let trgx : Trg;
    let trgy : Trg;
    // fast apply
    if self.get(trg).tag() == LAM {
      self.rwts.anni += 1;
      let got = self.swap(trg, NULL);
      trgx = Trg::Dir(Ptr::new(VR1, 0, got.loc()));
      trgy = Trg::Dir(Ptr::new(VR2, 0, got.loc()));
    } else {
      let k1 = self.alloc();
      trgx = Trg::Ptr(Ptr::new(VR1, 0, k1));
      trgy = Trg::Ptr(Ptr::new(VR2, 0, k1));
      self.safe_link(Trg::Ptr(Ptr::new(LAM, 0, k1)), trg);
    }
    let trgxx : Trg;
    let trgxy : Trg;
    // fast copy
    if self.get(trgx).tag() == NUM {
      self.rwts.comm += 1;
      let got = self.swap(trgx, NULL);
      trgxx = Trg::Ptr(got);
      trgxy = Trg::Ptr(got);
    } else {
      let k2 = self.alloc();
      trgxx = Trg::Ptr(Ptr::new(VR1, 0, k2));
      trgxy = Trg::Ptr(Ptr::new(VR2, 0, k2));
      self.safe_link(Trg::Ptr(Ptr::new(DUP, 3, k2)), trgx);
    }
    let k3 = self.alloc();
    let k4 = self.alloc();
    self.safe_link(Trg::Ptr(Ptr::new(VR2, 0, k4)), trgy);
    self.safe_link(Trg::Ptr(Ptr::new(VR1, 0, k4)), trgxy);
    self.safe_link(Trg::Ptr(Ptr::new(LAM, 0, k4)), Trg::Ptr(Ptr::new(VR2, 0, k3)));
    let k5 = self.alloc();
    self.safe_link(Trg::Ptr(Ptr::new(VR2, 0, k5)), Trg::Ptr(Ptr::big(REF, F_b)));
    self.safe_link(Trg::Ptr(Ptr::new(VR1, 0, k5)), Trg::Ptr(Ptr::big(REF, F_d)));
    self.safe_link(Trg::Ptr(Ptr::new(LAM, 0, k5)), Trg::Ptr(Ptr::new(VR1, 0, k3)));
    self.safe_link(Trg::Ptr(Ptr::new(MAT, 0, k3)), trgxx);
    return true;
  }

  pub fn L__U60.fib(&mut self, lab: Lab) -> bool {
    if lab == 0x5 { return true; }
    if lab == 0x3 { return true; }
    return false;
  }
  pub fn F__U60.fib(&mut self, ptr: Ptr, trg: Trg) -> bool {
    if self.get(trg).is_dup() && !self.L__U60.fib(self.get(trg).lab()) {
      self.copy(self.swap(trg, NULL), ptr);
      return true;
    }
    let k1 : Trg;
    let k2 : Trg;
    // fast match
    if self.get(trg).tag() == LAM && self.heap.get(self.get(trg).loc(), P1).is_num() {
      self.rwts.anni += 2;
      self.rwts.oper += 1;
      let got = self.swap(trg, NULL);
      let trgx = Trg::Dir(Ptr::new(VR1, 0, got.loc()));
      let trgy = Trg::Dir(Ptr::new(VR2, 0, got.loc()));
      if self.get(trgx).val() == 0 {
        self.swap(trgx, NULL);
        k1 = trgy;
        k2 = Trg::Ptr(ERAS);
      } else {
        self.swap(trgx, Ptr::big(NUM, self.get(trgx).val() - 1));
        k1 = Trg::Ptr(ERAS);
        k2 = trg;
      }
    } else {
      let k3 = self.alloc();
      let k4 = self.alloc();
      let k5 = self.alloc();
      self.heap.set(k3, P1, Ptr::new(MAT, 0, k4));
      self.heap.set(k3, P2, Ptr::new(VR2, 0, k4));
      self.heap.set(k4, P1, Ptr::new(LAM, 0, k5));
      self.heap.set(k4, P2, Ptr::new(VR2, 0, k3));
      self.safe_link(Trg::Ptr(Ptr::new(LAM, 0, k3)), trg);
      k1 = Trg::Ptr(Ptr::new(VR1, 0, k5));
      k2 = Trg::Ptr(Ptr::new(VR2, 0, k5));
    }
    // fast erase
    if self.get(k1).is_skp() {
      self.swap(k1, NULL);
      self.rwts.eras += 1;
    } else {
      self.safe_link(k1, Trg::Ptr(Ptr::new(NUM, 0x0, 0x0)));
    }
    self.safe_link(k2, Trg::Ptr(Ptr::big(REF, F_a)));
    return true;
  }

  pub fn L_b(&mut self, lab: Lab) -> bool {
    if lab == 0x5 { return true; }
    if lab == 0x3 { return true; }
    return false;
  }
  pub fn F_b(&mut self, ptr: Ptr, trg: Trg) -> bool {
    if self.get(trg).is_dup() && !self.L_b(self.get(trg).lab()) {
      self.copy(self.swap(trg, NULL), ptr);
      return true;
    }
    let trgx : Trg;
    let trgy : Trg;
    // fast apply
    if self.get(trg).tag() == LAM {
      self.rwts.anni += 1;
      let got = self.swap(trg, NULL);
      trgx = Trg::Dir(Ptr::new(VR1, 0, got.loc()));
      trgy = Trg::Dir(Ptr::new(VR2, 0, got.loc()));
    } else {
      let k1 = self.alloc();
      trgx = Trg::Ptr(Ptr::new(VR1, 0, k1));
      trgy = Trg::Ptr(Ptr::new(VR2, 0, k1));
      self.safe_link(Trg::Ptr(Ptr::new(LAM, 0, k1)), trg);
    }
    self.safe_link(trgy, Trg::Ptr(Ptr::big(REF, F_c)));
    // fast erase
    if self.get(trgx).is_skp() {
      self.swap(trgx, NULL);
      self.rwts.eras += 1;
    } else {
      self.safe_link(trgx, Trg::Ptr(Ptr::new(ERA, 0x0, 0x0)));
    }
    return true;
  }

  pub fn L_d(&mut self, lab: Lab) -> bool {
    return false;
  }
  pub fn F_d(&mut self, ptr: Ptr, trg: Trg) -> bool {
    if self.get(trg).is_dup() && !self.L_d(self.get(trg).lab()) {
      self.copy(self.swap(trg, NULL), ptr);
      return true;
    }
    let trgx : Trg;
    let trgy : Trg;
    // fast apply
    if self.get(trg).tag() == LAM {
      self.rwts.anni += 1;
      let got = self.swap(trg, NULL);
      trgx = Trg::Dir(Ptr::new(VR1, 0, got.loc()));
      trgy = Trg::Dir(Ptr::new(VR2, 0, got.loc()));
    } else {
      let k1 = self.alloc();
      trgx = Trg::Ptr(Ptr::new(VR1, 0, k1));
      trgy = Trg::Ptr(Ptr::new(VR2, 0, k1));
      self.safe_link(Trg::Ptr(Ptr::new(LAM, 0, k1)), trg);
    }
    // fast erase
    if self.get(trgy).is_skp() {
      self.swap(trgy, NULL);
      self.rwts.eras += 1;
    } else {
      self.safe_link(trgy, Trg::Ptr(Ptr::new(NUM, 0x1, 0x0)));
    }
    // fast erase
    if self.get(trgx).is_skp() {
      self.swap(trgx, NULL);
      self.rwts.eras += 1;
    } else {
      self.safe_link(trgx, Trg::Ptr(Ptr::new(ERA, 0x0, 0x0)));
    }
    return true;
  }

  pub fn L_c(&mut self, lab: Lab) -> bool {
    if lab == 0x5 { return true; }
    if lab == 0x3 { return true; }
    return false;
  }
  pub fn F_c(&mut self, ptr: Ptr, trg: Trg) -> bool {
    if self.get(trg).is_dup() && !self.L_c(self.get(trg).lab()) {
      self.copy(self.swap(trg, NULL), ptr);
      return true;
    }
    let _k1 : Trg = Trg::Ptr(Ptr::big(REF, F__U60.fib));
    let _k1x : Trg;
    let _k1y : Trg;
    // fast apply
    if self.get(_k1).tag() == LAM {
      self.rwts.anni += 1;
      let got = self.swap(_k1, NULL);
      _k1x = Trg::Dir(Ptr::new(VR1, 0, got.loc()));
      _k1y = Trg::Dir(Ptr::new(VR2, 0, got.loc()));
    } else {
      let k2 = self.alloc();
      _k1x = Trg::Ptr(Ptr::new(VR1, 0, k2));
      _k1y = Trg::Ptr(Ptr::new(VR2, 0, k2));
      self.safe_link(Trg::Ptr(Ptr::new(LAM, 0, k2)), _k1);
    }
    let k3 = self.alloc();
    self.safe_link(Trg::Ptr(Ptr::new(OP2, 0, k3)), _k1y);
    let _k4 : Trg = Trg::Ptr(Ptr::big(REF, F__U60.fib));
    let _k4x : Trg;
    let _k4y : Trg;
    // fast apply
    if self.get(_k4).tag() == LAM {
      self.rwts.anni += 1;
      let got = self.swap(_k4, NULL);
      _k4x = Trg::Dir(Ptr::new(VR1, 0, got.loc()));
      _k4y = Trg::Dir(Ptr::new(VR2, 0, got.loc()));
    } else {
      let k5 = self.alloc();
      _k4x = Trg::Ptr(Ptr::new(VR1, 0, k5));
      _k4y = Trg::Ptr(Ptr::new(VR2, 0, k5));
      self.safe_link(Trg::Ptr(Ptr::new(LAM, 0, k5)), _k4);
    }
    self.safe_link(_k4y, Trg::Ptr(Ptr::new(VR1, 0, k3)));
    let trgx : Trg;
    let trgy : Trg;
    // fast apply
    if self.get(trg).tag() == LAM {
      self.rwts.anni += 1;
      let got = self.swap(trg, NULL);
      trgx = Trg::Dir(Ptr::new(VR1, 0, got.loc()));
      trgy = Trg::Dir(Ptr::new(VR2, 0, got.loc()));
    } else {
      let k6 = self.alloc();
      trgx = Trg::Ptr(Ptr::new(VR1, 0, k6));
      trgy = Trg::Ptr(Ptr::new(VR2, 0, k6));
      self.safe_link(Trg::Ptr(Ptr::new(LAM, 0, k6)), trg);
    }
    self.safe_link(trgy, Trg::Ptr(Ptr::new(VR2, 0, k3)));
    let trgxx : Trg;
    let trgxy : Trg;
    // fast copy
    if self.get(trgx).tag() == NUM {
      self.rwts.comm += 1;
      let got = self.swap(trgx, NULL);
      trgxx = Trg::Ptr(got);
      trgxy = Trg::Ptr(got);
    } else {
      let k7 = self.alloc();
      trgxx = Trg::Ptr(Ptr::new(VR1, 0, k7));
      trgxy = Trg::Ptr(Ptr::new(VR2, 0, k7));
      self.safe_link(Trg::Ptr(Ptr::new(DUP, 5, k7)), trgx);
    }
    let k8 = self.alloc();
    self.safe_link(Trg::Ptr(Ptr::new(VR2, 0, k8)), _k4x);
    self.safe_link(Trg::Ptr(Ptr::new(VR1, 0, k8)), Trg::Ptr(Ptr::new(NUM, 0x2, 0x0)));
    self.safe_link(Trg::Ptr(Ptr::new(OP2, 1, k8)), trgxy);
    let k9 = self.alloc();
    self.safe_link(Trg::Ptr(Ptr::new(VR2, 0, k9)), _k1x);
    self.safe_link(Trg::Ptr(Ptr::new(VR1, 0, k9)), Trg::Ptr(Ptr::new(NUM, 0x1, 0x0)));
    self.safe_link(Trg::Ptr(Ptr::new(OP2, 1, k9)), trgxx);
    return true;
  }

}