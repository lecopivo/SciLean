import SciLean

open SciLean


variable
  {K : Type} [RCLike K]
  {X : Type} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type} [NormedAddCommGroup Y] [NormedSpace K Y]

set_default_scalar K


variable (f : X → Nat → Y) (x : X)

-- TODO: add option to lsimp not to destroy let bindings with lambdas
/--
info: let ydf := holdLet fun i => ∂ (x':=x), f x' i;
ydf 0 : X →L[K] Y
-/
#guard_msgs in
#check
  (let ydf := holdLet <| fun i => ∂ x':=x, f x' i; (ydf 0))
  rewrite_by
    lsimp

/--
info: let f := holdLet fun i => i;
f 0 : ℕ
-/
#guard_msgs in
#check
  (let f := holdLet <| fun i : Nat => i ; (f 0))
  rewrite_by
    autodiff
