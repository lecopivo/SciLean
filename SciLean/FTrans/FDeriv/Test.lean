import SciLean.FTrans.FDeriv.Basic
import SciLean.Profile

open SciLean


variable {K : Type _} [NontriviallyNormedField K]

variable {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
variable {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
variable {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]

variable {ι : Type _} [Fintype ι]

variable {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]

example : NormedCommRing K := by infer_instance
example : NormedAlgebra K K := by infer_instance

example 
  : fderiv K (fun (x : K) => x * x * x)
    =
    fun x => fun dx =>L[K] dx * x + dx * x  := 
by 
  ftrans only
  set_option trace.Meta.Tactic.simp.rewrite true in
  set_option trace.Meta.Tactic.simp.discharge true in
  set_option trace.Meta.Tactic.simp.unify true in
  set_option trace.Meta.Tactic.lsimp.pre true in
  set_option trace.Meta.Tactic.lsimp.step true in
  set_option trace.Meta.Tactic.lsimp.post true in
  ftrans only
  ext x; simp


example 
  : fderiv K (fun (x : K) => x + x)
    =
    fun x => fun dx =>L[K]
      dx + dx := 
by 
  ftrans only
  ext x; simp


example 
  : fderiv K (fun (x : K) => x + x + x)
    =
    fun x => fun dx =>L[K]
      dx + dx + dx := 
by 
  ftrans only
  ext x; simp

example 
  : fderiv K (fun (x : K) => x + x + x + x)
    =
    fun x => fun dx =>L[K]
      dx + dx + dx + dx := 
by 
  ftrans only
  ext x; simp

example 
  : fderiv K (fun (x : K) => x + x + x + x + x)
    =
    fun x => fun dx =>L[K]
      dx + dx + dx + dx + dx := 
by 
  ftrans only
  ext x; simp
