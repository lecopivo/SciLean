import SciLean.FTrans.FDeriv.Basic
import SciLean.Profile

open SciLean

-- #profile_this_file

set_option profiler true

variable {K : Type _} [NontriviallyNormedField K]

variable {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
variable {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
variable {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]

variable {ι : Type _} [Fintype ι]

variable {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]

#exits
-- example 
--   : fderiv K (fun (x : K) => x * x * x)
--     =
--     fun x => fun dx =>L[K] dx * x + dx * x  := 
-- by 
--   ftrans only
--   set_option trace.Meta.Tactic.simp.rewrite true in
--   set_option trace.Meta.Tactic.simp.discharge true in
--   set_option trace.Meta.Tactic.simp.unify true in
--   set_option trace.Meta.Tactic.lsimp.pre true in
--   set_option trace.Meta.Tactic.lsimp.step true in
--   set_option trace.Meta.Tactic.lsimp.post true in
--   ftrans only
--   ext x; simp

example : Differentiable K fun x : K => x := by fprop

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
  ftrans only;
  ext x; simp

example 
  : fderiv K (fun (x : K) => x * x * x * x)
    =
    fun x => fun dx =>L[K] 0 := 
by
  conv =>
    lhs
    ftrans only
  sorry


set_option trace.Meta.Tactic.simp.rewrite true in
example 
  : fderiv K (fun (x : K) => x + x + x + x)
    =
    fun x => fun dx =>L[K]
      dx + dx + dx + dx := 
by 
  ftrans


variable {K : Type _} [NontriviallyNormedField K]

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace K E]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace K F]

variable {G : Type _} [NormedAddCommGroup G] [NormedSpace K G]

variable {f f₀ f₁ g : E → F}

theorem fderiv_add' 
  (hf : Differentiable K f) (hg : Differentiable K g) :
    fderiv K (fun y => f y + g y) 
    = 
    fun x =>
    fun dx =>L[K] 
      fderiv K f x dx + fderiv K g x dx := sorry

example (x : K)
  : fderiv K (fun (x : K) => x + x + x + x + x) x
    =
    fun dx =>L[K]
      dx + dx + dx + dx + dx := 
by
  simp (discharger:=fprop) only [fderiv_add', fderiv_id']
  dsimp
