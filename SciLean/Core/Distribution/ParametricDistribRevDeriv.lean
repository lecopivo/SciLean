import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Distribution.ParametricDistribFwdDeriv
import SciLean.Core.Distribution.Eval

namespace SciLean


open MeasureTheory

namespace SciLean

open Distribution

variable
  {R} [RealScalar R]
  {W} [SemiInnerProductSpace R W]
  {X} [SemiInnerProductSpace R X]
  {Y} [SemiInnerProductSpace R Y] [Module ℝ Y]
  {Z} [SemiInnerProductSpace R Z] [Module ℝ Z]
  {U} [SemiInnerProductSpace R U] -- [Module ℝ U]
  {V} [SemiInnerProductSpace R V] -- [Module ℝ U]

set_default_scalar R


@[fun_trans]
noncomputable
def parDistribRevDeriv (f : X → 𝒟'(Y,Z)) (x : X) : 𝒟'(Y,Z×(Z→X)) :=
  ⟨fun φ =>
      let dz := semiAdjoint R (fun dx => cderiv R (f · φ) x dx)
      let z  := f x φ
      (z, dz), sorry_proof⟩


namespace parDistribRevDeriv


theorem comp_rule
    (f : Y → 𝒟'(Z,U)) (g : X → Y)
    (hf : DistribDifferentiable f) (hg : HasAdjDiff R g) :
    parDistribRevDeriv (fun x => f (g x))
    =
    fun x =>
      let ydg := revDeriv R g x
      let udf := parDistribRevDeriv f ydg.1
      udf.postComp (⟨fun (u,df') => (u, fun du => ydg.2 (df' du)), by sorry_proof⟩) := by

  unfold parDistribRevDeriv postComp
  funext x; ext φ
  simp
  fun_trans
  simp [action_push,revDeriv,fwdDeriv]
  have : ∀ x, HasSemiAdjoint R (∂ x':=x, f x' φ) := sorry_proof -- todo add: `DistribHasAdjDiff`
  have : ∀ φ, CDifferentiable R fun x0 => (f x0) φ := sorry_proof
  fun_trans



theorem bind_rule
    (f : X → Y → 𝒟'(Z,V)) (g : X → 𝒟'(Y,U)) (L : U ⊸ V ⊸ W) :
    parDistribRevDeriv (fun x => (g x).bind (f x) L)
    =
    fun x =>
      let ydg := parDistribRevDeriv g x
      let zdf := fun y => parDistribRevDeriv (f · y) x
      ydg.bind zdf (⟨fun (u,dg) => ⟨fun (v,df) =>
        (L u v, fun dw =>
                  df (semiAdjoint R (L u ·) dw) +
                  dg (semiAdjoint R (L · v) dw)), sorry_proof⟩, sorry_proof⟩) := by

  unfold parDistribRevDeriv Distribution.bind
  funext x; ext φ
  simp
  sorry_proof
  sorry_proof



----------------------------------------------------------------------------------------------------
-- Dirac -------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

noncomputable
def diracRevDeriv (x : X) : 𝒟'(X,R×(R→X)) :=
  ⟨fun φ => revDeriv R φ x, sorry_proof⟩


@[fun_trans]
theorem dirac.arg_xy.parDistribRevDeriv_rule
    (x : W → X) (hx : HasAdjDiff R x) :
    parDistribRevDeriv (fun w => dirac (x w) (R:=R))
    =
    fun w =>
      let xdx := revDeriv R x w
      diracRevDeriv xdx.1 |>.postComp (⟨fun (r,dφ) => (r, fun dr => xdx.2 (dφ dr)), sorry_proof⟩) := by

  funext w; apply Distribution.ext _ _; intro φ
  have : HasAdjDiff R φ := sorry_proof -- this should be consequence of that `R` has dimension one
  simp [diracRevDeriv,revDeriv, parDistribRevDeriv, postComp]
  fun_trans
