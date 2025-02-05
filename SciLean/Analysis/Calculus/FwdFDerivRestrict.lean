import SciLean.Tactic.StructureDecomposition
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.Notation.FwdDeriv

open SciLean

variable
  {R : Type*} [RealScalar R]
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
