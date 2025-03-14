import SciLean

open SciLean


set_default_scalar Float


noncomputable
def foo := (∇ (x:= ⊞[1.0,2,3,4]), IdxType.fold .full (init:=1.0) (fun i s => s * x[i]))


/-- info: ⊞[24.000000, 12.000000, 8.000000, 6.000000] -/
#guard_msgs in
#eval foo
  rewrite_by
    unfold foo fgradient
    lsimp -zeta only [simp_core, ↓revFDeriv_simproc]

attribute [data_synth high] SciLean.IdxType.fold.arg_initf.HasRevFDeriv_scalar_rule


/-- info: ⊞[24.000000, 12.000000, 8.000000, 6.000000] -/
#guard_msgs in
#eval foo
  rewrite_by
    unfold foo fgradient
    lsimp -zeta only [simp_core, ↓revFDeriv_simproc]
