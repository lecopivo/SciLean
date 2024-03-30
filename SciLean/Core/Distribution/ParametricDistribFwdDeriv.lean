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
  {V} [Vec R V] -- [Module ℝ U]

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


@[simp, ftrans_simp]
theorem asdf (u : 𝒟'(X,Y)) (f : Y → Z) (φ : 𝒟 X) :
    (u.postComp f).action φ = f (u.action φ) := sorry_proof


@[simp, ftrans_simp]
theorem asdf' (u : 𝒟'(X,Y)) (f : Y → Z) (φ : X → R) :
    (u.postComp f).extAction φ = f (u.extAction φ) := sorry_proof


@[simp, ftrans_simp]
theorem asdf'' (u : 𝒟'(X,U)) (f : U → Y) (φ : X → Z) (L : Y → Z → W) :
    (u.postComp f).extAction' φ L = u.extAction' φ (fun u z => L (f u) z) := sorry_proof


@[simp, ftrans_simp]
theorem asdf''' (u : 𝒟'(X,Y)) (φ : X → U) (ψ : X → V) (L : Y → (U×V) → W) :
    u.extAction' (fun x => (φ x, ψ x)) L
    =
    u.extAction' φ (fun y u => L y (u,0))
    +
    u.extAction' ψ (fun y v => L y (0,v)) := sorry_proof

@[simp, ftrans_simp]
theorem asdf'''' (u : 𝒟'(X,Y)) (φ : X → R) (L : Y → R → Y) :
    u.extAction' φ L
    =
    L (u.extAction φ) 1 := sorry_proof


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
  simp only [ftrans_simp, action_push]
  simp only [ftrans_simp, action_push]




theorem bind_rule'
    (f : X → Y → 𝒟'(Z,V)) (g : X → 𝒟'(Y,U)) (L : U → V → W)
    (hf : DistribDifferentiable (fun (x,y) => f x y)) (hg : DistribDifferentiable g)
    (hL₁ : ∀ u, IsSmoothLinearMap R (L u ·)) (hL₂ : ∀ v, IsSmoothLinearMap R (L · v)) :
    parDistribFwdDeriv (fun x => (g x).bind' (f x) L)
    =
    fun x dx =>
      let ydy := parDistribFwdDeriv g x dx
      let zdz := fun y => parDistribFwdDeriv (f · y) x dx
      ydy.bind' zdz (fun (r,dr) (s,ds) => (L r s, L r ds + L dr s)) := sorry_proof
