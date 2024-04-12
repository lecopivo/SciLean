import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Distribution.ParametricDistribFwdDeriv
import SciLean.Core.Distribution.Eval

namespace SciLean

open MeasureTheory Distribution

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
def parDistribRevDeriv (f : X → 𝒟'(Y,Z)) (x : X) : 𝒟'(Y,Z×(Z⊸X)) :=
  ⟨fun φ =>
      let df' := semiAdjoint R (fun dx => cderiv R (f · φ) x dx)
      let z  := f x φ
      (z, fun dz ⊸ df' dz), sorry_proof⟩


namespace parDistribRevDeriv


----------------------------------------------------------------------------------------------------
-- Composition -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

theorem comp_rule
    (f : Y → 𝒟'(Z,U)) (g : X → Y)
    (hf : DistribDifferentiable f) (hg : HasAdjDiff R g) :
    parDistribRevDeriv (fun x => f (g x))
    =
    fun x =>
      let ydg := revDeriv' R g x
      let udf := parDistribRevDeriv f ydg.1
      udf.postComp (fun udf' ⊸ (udf'.1, fun du ⊸ ydg.2 (udf'.2 du))) := by

  simp
  unfold parDistribRevDeriv postComp
  funext x; ext φ
  simp
  sorry_proof -- TODO: fix fun_trans bug
  -- fun_trans
  -- simp [action_push,revDeriv,fwdDeriv]
  -- have : ∀ x, HasSemiAdjoint R (∂ x':=x, f x' φ) := sorry_proof -- todo add: `DistribHasAdjDiff`
  -- have : ∀ φ, CDifferentiable R fun x0 => (f x0) φ := sorry_proof
  -- fun_trans


----------------------------------------------------------------------------------------------------
-- Bind --------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

theorem bind_rule
    (f : X → Y → 𝒟'(Z,V)) (g : X → 𝒟'(Y,U)) (L : U ⊸ V ⊸ W) :
    parDistribRevDeriv (fun x => (g x).bind (f x) L)
    =
    fun x =>
      let ydg := parDistribRevDeriv g x
      let zdf := fun y => parDistribRevDeriv (f · y) x
      ydg.bind zdf (⟨fun (u,dg) => ⟨fun vdf =>
        (L u vdf.1, fun dw ⊸
                  vdf.2 (semiAdjoint R (L u ·) dw) +
                  dg (semiAdjoint R (L · vdf.1) dw)), sorry_proof⟩, sorry_proof⟩) := by

  unfold parDistribRevDeriv Distribution.bind
  funext x; ext φ
  simp
  sorry_proof
  sorry_proof



----------------------------------------------------------------------------------------------------
-- Dirac -------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

noncomputable
def diracRevDeriv (x : X) : 𝒟'(X,R×(R⊸X)) :=
  ⟨fun φ => revDeriv' R φ x, sorry_proof⟩

@[fun_trans]
theorem dirac.arg_xy.parDistribRevDeriv_rule
    (x : W → X) (hx : HasAdjDiff R x) :
    parDistribRevDeriv (fun w => dirac (x w) (R:=R))
    =
    fun w =>
      let xdx := revDeriv' R x w
      diracRevDeriv xdx.1 |>.postComp (⟨fun (r,dφ) => (r, fun dr ⊸ xdx.2 (dφ dr)), sorry_proof⟩) := by

  funext w; apply Distribution.ext _ _; intro φ
  have : HasAdjDiff R φ := sorry_proof -- this should be consequence of that `R` has dimension one
  simp [diracRevDeriv,revDeriv, parDistribRevDeriv, postComp]
  sorry_proof -- fix fun_trans bug "unexpected bound variable #0"
  -- fun_trans


----------------------------------------------------------------------------------------------------
-- Integral ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


variable [MeasureSpace X] [MeasureSpace Y]

@[fun_trans]
theorem cintegral.arg_f.revDeriv_distrib_rule (f : W → X → Y) :
    revDeriv R (fun w => ∫' x, f w x)
    =
    fun w =>
      let ydf := (parDistribRevDeriv (fun w => (f w ·).toDistribution (R:=R)) w).integrate
      (ydf.1, fun dy => ydf.2 dy) := sorry_proof

@[fun_trans]
theorem cintegral.arg_f.parDistribRevDeriv_rule (f : W → X → Y → Z) :
    parDistribRevDeriv (fun w => (fun x => ∫' y, f w x y).toDistribution (R:=R))
    =
    fun w =>
      let Tf := (fun w => (fun x => (fun y => f w x y).toDistribution (R:=R)).toDistribution (R:=R))
      (parDistribRevDeriv Tf w).postComp
        ⟨fun (z,df) => (z.integrate, ⟨fun dz => df (fun _ => dz).toDistribution, sorry_proof⟩), sorry_proof⟩ := sorry_proof


-- I'm not sure if this is correct
-- I have a feeling that `B` is supposed to be used in the reverse pass somehow
@[fun_trans]
theorem cintegral.arg_f.parDistribRevDeriv_rule' (f : W → X → Y → Z) (B : X → Set Y) :
    parDistribRevDeriv (fun w => (fun x => ∫' y in B x, f w x y).toDistribution (R:=R))
    =
    fun w =>
      let Tf := (fun w => (fun x => ((fun y => f w x y).toDistribution (R:=R)).restrict (B x)).toDistribution (R:=R))
      (parDistribRevDeriv Tf w).postComp
        ⟨fun (z,df) => (z.integrate, ⟨fun dz => df (fun _ => dz).toDistribution,sorry_proof⟩), sorry_proof⟩ := sorry_proof



----------------------------------------------------------------------------------------------------
-- Add ---------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.parDistribDeriv_rule (f g : W → 𝒟'(X,Y))
    (hf : DistribDifferentiable f) (hg : DistribDifferentiable g) :
    parDistribRevDeriv (fun w => f w + g w)
    =
    fun w =>
      let ydf := parDistribRevDeriv f w
      let ydg := parDistribRevDeriv g w
      ydf + ydg := by
  funext w; ext φ; simp[parDistribRevDeriv]
  simp[parDistribRevDeriv]
  sorry_proof
