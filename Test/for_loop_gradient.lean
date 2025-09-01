import SciLean

open SciLean

set_default_scalar Float

#exit

def foo :=
  ((SciLean.gradient Float (fun x : Float^[3] => Id.run do
    let mut prod := 1.0
    let mut sum := 0.0
    for i in IndexType.univ (Fin 3) do
      prod := prod * x[i]
      sum := sum + x[i]
    (prod,sum)))
    rewrite_by
      unfold SciLean.gradient
      autodiff
      unfold SciLean.gradient)

/--
info: ⊞[56.000000, 48.000000, 42.000000]
-/
#guard_msgs in
#eval foo ⊞[6.0,7,8] (1,0)

/--
info: ⊞[0.000000, 0.000000, 0.000000]
-/
#guard_msgs in
#eval foo ⊞[6.0,7,8] (0,0)

def bar :=
  ((SciLean.gradient Float (fun x : Float ^ Idx 3 => Id.run do
    let mut prod := 1
    let mut sum := 0.0
    let mut norm2 := 0.0
    -- let mut norm2 := 0.0
    for i in fullRange (Idx 3) do
      prod := prod * x[i]
      sum := sum + x[i]
      norm2 := norm2 + x[i]*x[i]
    (prod,sum,norm2)))
    rewrite_by
      unfold SciLean.gradient
      fun_trans
      fun_trans
      unfold SciLean.gradient
      fun_trans)

/--
info: ⊞[56.000000, 48.000000, 42.000000]
-/
#guard_msgs in
#eval (bar ⊞[6.0, 7, 8] (1,0,0))

/--
info: ⊞[1.000000, 1.000000, 1.000000]
-/
#guard_msgs in
#eval (bar ⊞[6.0, 7, 8] (0,1,0))

/--
info: ⊞[12.000000, 14.000000, 16.000000]
-/
#guard_msgs in
#eval (bar ⊞[6.0, 7, 8] (0,0,1))
