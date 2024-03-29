import SciLean.Core.Distribution.ParametricDistribDeriv

namespace SciLean


open MeasureTheory

namespace SciLean

open Distribution

variable
  {R} [RealScalar R]
  {W} [Vec R W]
  {X} [Vec R X]
  {Y} [Vec R Y] [Module ℝ Y]
  {Z} [Vec R Z] [Module ℝ Z]
  {U} [Vec R U] -- [Module ℝ U]

set_default_scalar R


@[fun_trans]
noncomputable
def parDistribFwdDeriv (f : X → 𝒟'(Y,Z)) (x dx : X) : 𝒟'(Y,Z×Z) :=
  let dz := parDistribDeriv f x dx |>.postComp (fun dz => ((0:Z),dz))
  let z  := f x |>.postComp (fun z => (z,(0:Z)))
  z + dz




namespace parDistribFwdDeriv


theorem comp_rule
    (f : Y → 𝒟'(Z,U)) (g : X → Y)
    (hf : DistribDifferentiable f) (hg : CDifferentiable R g) :
    parDistribFwdDeriv (fun x => f (g x))
    =
    fun x dx =>
      let ydy := fwdDeriv R g x dx
      parDistribFwdDeriv f ydy.1 ydy.2 := by

  unfold parDistribFwdDeriv
  funext x dx
  fun_trans [action_push,fwdDeriv]



theorem bind_rule
    (f : X → Y → 𝒟' Z) (g : X → 𝒟' Y)
    (hf : DistribDifferentiable (fun (x,y) => f x y)) (hg : DistribDifferentiable g) :
    parDistribFwdDeriv (fun x => (g x).bind (f x))
    =
    fun x dx =>
      let ydy := parDistribFwdDeriv g x dx
      let zdz := fun y => parDistribFwdDeriv (f · y) x dx
      ydy.bind' zdz (fun (r,dr) (s,ds) => (r*s, r*ds + s*dr)) := by

  unfold parDistribFwdDeriv Distribution.bind'
  autodiff
  funext x dx
  fun_trans [action_push,fwdDeriv]
  ext φ
  simp [action_push]
  sorry_proof
