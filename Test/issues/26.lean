module

public import SciLean

@[expose] public section


open SciLean

variable (a : Nat)

/--
info: let x := a + a;
a + (a + x) : ℕ
-/
#guard_msgs in
#check
  (a +
    (a +
    let x := a + a
    x))
  rewrite_by
    lsimp
