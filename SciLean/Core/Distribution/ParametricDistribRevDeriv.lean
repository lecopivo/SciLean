import SciLean.Core.Distribution.ParametricDistribDeriv

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
  ⟨⟨fun φ =>
      let dz := semiAdjoint R (fun dx => ⟪parDistribDeriv f x dx,φ⟫)
      let z  := ⟪f x, φ⟫
      (z, sorry), sorry_proof⟩⟩



namespace parDistribRevDeriv


theorem comp_rule
    (f : Y → 𝒟'(Z,U)) (g : X → Y)
    (hf : DistribDifferentiable f) (hg : CDifferentiable R g) :
    parDistribRevDeriv (fun x => f (g x))
    =
    fun x =>
      let ydg := revDeriv R g x
      let udf := parDistribRevDeriv f ydg.1
      udf.postComp (fun (u,df') => (u, fun du => ydg.2 (df' du))) := by sorry_proof


theorem bind_rule
    (f : X → Y → 𝒟' Z) (g : X → 𝒟' Y) :
    parDistribRevDeriv (fun x => (g x).bind (f x))
    =
    fun x =>
      let ydg := parDistribRevDeriv g x
      let zdf := fun y => parDistribRevDeriv (f · y) x
      ydg.bind' zdf (fun (_,dg) (z,df) => (z, fun dr => dg dr + df dr)) := sorry_proof
