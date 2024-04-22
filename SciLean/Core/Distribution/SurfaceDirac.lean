import SciLean.Core.Distribution.Basic
import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Integral.Surface
import SciLean.Core.Integral.MovingDomain
import SciLean.Core.Integral.Jacobian
import SciLean.Core.Integral.PlaneDecomposition


open MeasureTheory FiniteDimensional

namespace SciLean

variable
  {R} [RealScalar R]
  {W} [Vec R W] [Module ℝ W]
  {X} [SemiHilbert R X] [MeasureSpace X]
  {Y} [Vec R Y] [Module ℝ Y]
  {Z} [Vec R Z] [Module ℝ Z]
  {U} [Vec R U]
  {V} [Vec R V]

set_default_scalar R


open Classical
noncomputable
def surfaceDirac (A : Set X) (f : X → Y) (d : ℕ) : 𝒟'(X,Y) :=
  fun φ ⊸ ∫' x in A, φ x • f x ∂(surfaceMeasure d)


open Classical
noncomputable
def surfaceDirac' (A : Set X) (f : X → R) (u : 𝒟'(X,Y)) (d : ℕ) : 𝒟'(X,Y) := sorry
  -- fun φ ⊸ ∫' x in A, φ x • f x ∂(surfaceMeasure d)


@[action_push]
theorem surfaceDirac_action (A : Set X) (f : X → Y) (d : ℕ) (φ : 𝒟 X) :
    (surfaceDirac A f d) φ = ∫' x in A, φ x • f x ∂(surfaceMeasure d) := sorry_proof


@[action_push]
theorem surfaceDirac_extAction (A : Set X) (f : X → Y) (d : ℕ) (φ : X → V) (L : Y ⊸ V ⊸ W) :
    (surfaceDirac A f d).extAction φ L = ∫' x in A, L (f x) (φ x) ∂(surfaceMeasure d) := sorry_proof


@[simp, ftrans_simp]
theorem surfaceDirac_dirac (f : X → Y) (x : X) : surfaceDirac {x} f 0 = (dirac x).postComp (fun r ⊸ r • (f x)) := by
  ext φ
  unfold surfaceDirac; dsimp
  sorry_proof


theorem iteD.arg_cte.parDistribDeriv_rule
    (s : W → Set X) (t e : W → 𝒟'(X,R))
    (ht : DistribDifferentiable t) (he : DistribDifferentiable e) :
    parDistribDeriv (fun w => ifD s w then t w else e w)
    =
    fun w dw =>
      -- !!!THiS IS INCORRECT!!! it should contain term `t w - e w` but it is not clear how to consume it
      surfaceDirac (frontier (s w)) (fun x => (frontierSpeed R s w dw x)) (finrank R X - 1)
      +
      ifD s w then
        parDistribDeriv t w dw
      else
        parDistribDeriv e w dw := sorry


open Classical Function in
@[fun_trans]
theorem ite_parDistribDeriv (A : W → Set X) (f g : W → X → Y) :
    parDistribDeriv (fun w => Function.toDistribution (fun x => if x ∈ A w then f w x else g w x))
    =
    fun w dw =>
      surfaceDirac (frontier (A w)) (fun x => (frontierSpeed R A w dw x) • (f w x - g w x)) (finrank R X - 1)
      +
      ifD (A w) then
        (parDistribDeriv (fun w => (f w ·).toDistribution (R:=R)) w dw)
      else
        (parDistribDeriv (fun w => (g w ·).toDistribution (R:=R)) w dw) := sorry_proof


open Function in
@[fun_trans]
theorem ite_parDistribDeriv' (φ ψ : W → X → R) (f g : W → X → Y) :
    parDistribDeriv (fun w => Function.toDistribution (fun x => if φ w x ≤ ψ w x then f w x else g w x))
    =
    fun w dw =>
      let frontierSpeed := fun x => - (∂ (w':=w;dw), (φ w' x - ψ w' x)) / ‖∇ (x':=x), (φ w x' - ψ w x')‖₂
      (surfaceDirac {x | φ w x = ψ w x} (fun x => frontierSpeed x • (f w x - g w x)) (finrank R X - 1))
      +
      ifD {x | φ w x ≤ ψ w x} then
        (parDistribDeriv (fun w => (f w ·).toDistribution (R:=R)) w dw)
      else
        (parDistribDeriv (fun w => (g w ·).toDistribution (R:=R)) w dw) := sorry_proof


open Function in
@[fun_trans]
theorem toDistribution.arg_f.parDistribDeriv_rule (f : W → X → Y) (hf : ∀ x, CDifferentiable R (f · x)) :
    parDistribDeriv (fun w => Function.toDistribution (fun x => f w x))
    =
    fun w dw =>
      (Function.toDistribution (fun x => cderiv R (f · x) w dw) (R:=R)) := by

  unfold parDistribDeriv
  funext x dx; ext φ
  simp[Function.toDistribution]
  sorry_proof


----------------------------------------------------------------------------------------------------
-- Substitution ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


variable
  {I} [Fintype I]
  {X₁ : I → Type} [∀ i, SemiHilbert R (X₁ i)] [∀ i, MeasureSpace (X₁ i)]
  {X₂ : I → Type} [∀ i, Vec R (X₂ i)]

-- open BigOperators in
-- theorem intetgral_parametric_inverse [Fintype I] (φ ψ : X → W) (f : X → Y) (hdim : d = finrank R X - finrank R W)
--   {p : (i : I) → X₁ i → X₂ i → X} {ζ : (i : I) → X₁ i → X₂ i} {dom : (i : I) → Set (X₁ i)}
--   (inv : ParametricInverseAt (fun x => φ x - ψ x) 0 p ζ dom) :
--   ∫' x in {x' | φ x' = ψ x'}, f x ∂(surfaceMeasure d)
--   =
--   ∑ i, ∫' x₁ in dom i, jacobian R (fun x => p i x (ζ i x)) x₁ • f (p i x₁ (ζ i x₁)) := sorry_proof
set_option pp.universes true in

open BigOperators in
theorem surfaceDirac_substitution [Fintype I] (φ ψ : X → R) (f : X → Y) (d : ℕ)
    {p : (i : I) → X₁ i → X₂ i → X} {ζ : (i : I) → X₁ i → X₂ i} {dom : (i : I) → Set (X₁ i)}
    (inv : ParametricInverseAt (fun x => φ x - ψ x) 0 p ζ dom) : -- (hdim : ∀ i, d = finrank R (X₁ i)) :
    surfaceDirac {x | φ x = ψ x} f d
    =
    ∑ i, Distribution.prod
           (fun x₁ x₂ => p i x₁ x₂)
           (((fun x₁ => jacobian R (fun x => p i x (ζ i x)) x₁ • f (p i x₁ (ζ i x₁))).toDistribution).restrict (dom i))
           (fun x₁ => (dirac (ζ i x₁) : 𝒟' (X₂ i)))
           (fun y ⊸ fun r ⊸ r • y) := sorry_proof




-- WIP: this simproc is under construction!
open Lean Meta Elab Term in
simproc_decl surfaceDirac_substitution_simproc (surfaceDirac {x | _ = _} _ _) := fun e => do
  IO.println s!"detected surfaceDirac in:\n{← ppExpr e}"

  let A := e.getRevArg! 2
  let f := e.getRevArg! 1
  let d := e.getRevArg! 0
  unless A.isAppOfArity ``setOf 2 do return .continue
  let φψ := A.appArg!

  lambdaTelescope φψ fun xs b => do
    unless b.isAppOfArity ``Eq 3 do return .continue

    let lhs := b.appFn!.appArg!
    let rhs := b.appArg!
    let φ ← mkLambdaFVars xs lhs
    let ψ ← mkLambdaFVars xs rhs
    let L ← mkLambdaFVars xs (← mkAppM ``HSub.hSub #[lhs,rhs])

    let R ← inferType lhs
    let is_affine ← mkAppM ``IsAffineMap #[R,L]

    IO.println s!"function {← ppExpr L}"
    IO.println s!"affine condition {← ppExpr is_affine}"

    let (.some ⟨proof⟩, _) ← (Mathlib.Meta.FunProp.funProp is_affine).run {} {}
      | IO.println "failed to prove affine condition!"
        return .continue

    IO.println s!"affine condition proven! {← ppExpr (← instantiateMVars proof)}"

    let parametric_inverse ← mkAppM ``parametric_inverse_affine' #[L, proof]

    IO.println s!"parametric inverse:\n{← ppExpr (← inferType parametric_inverse)}"

    let dirac_subst ← mkAppM ``surfaceDirac_substitution #[φ,ψ,f,d,parametric_inverse]

    let rule ← inferType dirac_subst
    let lhs := rule.appFn!.appArg!
    let rhs := rule.appArg!

    IO.println s!"old expr:\n{← ppExpr e}"
    IO.println s!"old expr':\n{← ppExpr lhs}"
    IO.println s!"new expr':\n{← ppExpr rhs}"

    if (← isDefEq e lhs) then
      return .visit { expr := rhs, proof? := dirac_subst }
    else
      return .continue


#exit

set_option trace.Meta.Tactic.simp.discharge true in
#check (parDistribDeriv (fun w : R =>
  Function.toDistribution
    fun x : R =>
      if 0 ≤ x - w then
        if 0 ≤ x^2 - w^2 then
          if 0 ≤ x^2 + w^2 then
            x + w
          else
            x - w
        else
          x / w
      else
        x * w))
  rewrite_by
    fun_trans (disch:=sorry) only [scalarGradient, ftrans_simp]
    simp only [ftrans_simp, finrank_self, le_refl, tsub_eq_zero_of_le]




set_option trace.Meta.Tactic.simp.discharge true in
#check (cderiv R (fun w : R =>
  ∫' (x : R) in Set.Icc 0 1,
      if 0 ≤ x - w then
        if 0 ≤ x^2 - w^2 then
          if 0 ≤ x^2 + w^2 then
            x + w
          else
            x - w
        else
          x / w
      else
        x * w))
  rewrite_by
    autodiff
    unfold scalarGradient
    autodiff
    -- fun_trans (disch:=sorry) only [scalarGradient, ftrans_simp]
    simp (config:={zeta:=false}) only [ftrans_simp, finrank_self, le_refl, tsub_eq_zero_of_le]
    simp (config:={zeta:=false}) only [ftrans_simp, action_push]
