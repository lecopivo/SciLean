import SciLean


variable (a : Nat)

/- expected
info: let x := a + a;
a + (a + x) : ℕ
-/

/--
info: a +
  let x := a + a;
  a + x : ℕ
-/
#guard_msgs in
#check 
  (a + 
    (a + 
    let x := a + a
    x))
  rewrite_by
    lsimp (config := {zeta := false, singlePass := true})
