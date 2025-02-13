import SciLean.Modules.ML.Dense

open SciLean

set_default_scalar Float

def test1 : IO Unit := do

  let A := ⊞[1.0,2.0;3.0,4.0]
  let b := ⊞[100.0,200.0]
  let x := ⊞[1.0,1.0]
  let dx := ⊞[0.1,0.1]

  let ydy := (∂> (ML.dense _ A b ·) x dx) rewrite_by autodiff

  let dy' := (<∂! (ML.dense _ A b ·) x).2 dx

  IO.println ydy
  IO.println dy'

  if ‖⊞[0.400000, 0.600000] - dy'‖₂ ≤ 1e-8 then
    IO.println "correct!"
  else
    IO.throwServerError "failed!"

/--
info: (⊞[103.000000, 207.000000], ⊞[0.300000, 0.700000])
⊞[0.400000, 0.600000]
correct!
-/
#guard_msgs in
#eval test1

def A := ⊞[1.0,2.0;3.0,4.0]

/-- info: 2.000000 -/
#guard_msgs in
#eval A[0,1]

/-- info: 2.000000 -/
#guard_msgs in
#eval A.curry[0][1]
