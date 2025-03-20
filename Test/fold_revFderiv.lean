import SciLean
import SciLean.Data.ArrayOperations.Operations.MapIdxMono

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


set_option pp.proofs false


#check (<∂ x : Float^[10],
     let x := x + x
     let y := ⊞ i => x[i]^2
     x.rmap2 (·*·) y)
  rewrite_by
    unfold DataArrayN.rmap2
    lsimp -zeta only [simp_core, ↓revFDeriv_simproc]


#check (<∂ x : Float^[10]×Float^[10],
     x.1.rmapIdx (fun i _ xi => xi^2*x.2[i]))
  rewrite_by
    unfold DataArrayN.rmap2
    lsimp -zeta only [simp_core, ↓revFDeriv_simproc,fromIdx]


#check (<∂ x : Float^[10]×Float^[10],
       x.1.rmap2 (·/·) x.2)
  rewrite_by
    unfold DataArrayN.rmap2; dsimp
    lsimp -zeta (disch:=unsafeAD) only [simp_core, ↓revFDeriv_simproc,fromIdx]
