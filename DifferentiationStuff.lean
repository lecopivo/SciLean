import SciLean
import Lean.Meta
import Mathlib.Tactic.MoveAdd
open SciLean

open Lean Elab Term Syntax Meta Command

variable {R} [RealScalar R]
set_default_scalar R

section RestrictTheorem
variable
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace R Y]
  {X₁ : Type*} [NormedAddCommGroup X₁] [NormedSpace R X₁]
  {X₂ : Type*} [NormedAddCommGroup X₂] [NormedSpace R X₂]

theorem fwdFDeriv_restrict''''
    (f : X → Y)
    (p : X → X₁) (hp : IsContinuousLinearMap R p)
    (g : X₁ → Y) (hg : Differentiable R g) (hg' : ∀ x, g (p x) = f x) :
    fwdFDeriv R f
    =
    fun x dx =>
      let x₁ := p x
      let dx₁ := p dx
      fwdFDeriv R g x₁ dx₁ := by

  funext x dx;
  conv => lhs; enter [2,x]; rw[←hg' x]
  fun_trans
end RestrictTheorem

variable (a b c d : R) (da db dc dd: R)



section RestrictTheorem
variable
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace R Y]
  {X₁ : Type*} [NormedAddCommGroup X₁] [NormedSpace R X₁]
  {X₂ : Type*} [NormedAddCommGroup X₂] [NormedSpace R X₂]

theorem fwdFDeriv_restrict
    (f : X → Y)
    (p : X → X₁) (g : X₁ → Y) (hg' : ∀ x, g (p x) = f x) (hp : IsContinuousLinearMap R p := by continuity)
   (hg : Differentiable R g := by continuity) :
    fwdFDeriv R f
    =
    fun x dx =>
      let x₁ := p x
      let dx₁ := p dx
      fwdFDeriv R g x₁ dx₁ := by

  funext x dx;
  conv => lhs; enter [2,x]; rw[←hg' x]
  fun_trans
end RestrictTheorem

open Qq Lean Meta Elab Tactic in
simproc_decl restrict_domain (@fwdFDeriv _ _ (_ × _) _ _ _ _ _ _) := fun e => do
  match e with
  | .app (.app (.app (.app (.app (.app (.app
    (.app (.app (.const `SciLean.fwdFDeriv _) K) _) X) _) _) Y) _) _) f =>
    let .some fac ← factorDomainThroughProjections f
      | return .continue
    let new_thm : Expr ← mkAppOptM ``fwdFDeriv_restrict
      #[K, none, X, none, none, Y, none, none, none, none, none, f, fac.dec.p₁, fac.f', fac.proof]
    let remaining_args₁ ← arrowDomainsN 2 <| ← inferType new_thm
    let hp₁ ← mkFreshExprMVar <| remaining_args₁.get! 0
    let hp₂ ← mkFreshExprMVar <| remaining_args₁.get! 1
    let new_thm : Expr ← mkAppM' new_thm #[hp₁, hp₂]
    return .visit { expr := (← inferType new_thm).getAppArgs.get! 2, proof? := some new_thm }
  | _ => return .continue


#check (∂> (x:=(a,b,c,d);(da,db,dc,dd)), (x.1 + x.2.2.2),
        ∂> x : R, x)
  rewrite_by
    simp (disch := fun_prop) [restrict_domain]
    trace_state
