test0
: ∀(A: *)
  ∀(B: *)
  ∀(aa: ∀(x:A) A)
  ∀(ab: ∀(x:A) B)
  ∀(ba: ∀(x:B) A)
  ∀(bb: ∀(x:B) B)
  ∀(a: A)
  ∀(b: B)
  A
= λA λB λaa λab λba λbb λa λb
  (aa (ab (aa (aa a))))
