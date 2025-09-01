import SciLean.Analysis.Diffeology.Basic
-- import SciLean.Analysis.Diffeology.DiffeologyMap

/-!

# Tangent bundle of diffeological space and derivative map

Tangent bundle of diffeological space. It allows us to talk about derivative as a function between
two tangent spaces.

NOTE: We also define separete notion of `TangentSpace` which should be equivalent to `TangentBundle`
      - for `TX : X → Type` and `TangentSpace X TX` we have `TangentBundle X (Σ x, TX x)`
      - for `TX : Type` and `TangentBundle X TX` we have `TangentSpace X (fun x => {dx : TX // π dx = x})`
      We have both definitions to figure out which one is easier to work with.


TODO: The paper 'Tangent spaces and tangent bundles for diffeological spaces'[1]  defines internal
      and external notion of tangent space. Figure out if our definition relates to theirs.

      [1] https://arxiv.org/abs/1411.5425
-/


namespace SciLean

local notation:max "ℝ^" n:max => (Fin n) → ℝ

/-- `E` is a fiber bundle over `B` -/
class FiberBundle (B : outParam (Type u)) (E : Type v) where
  proj : E → B

open FiberBundle in
/-- `ConeBundle B E` says that `E` is a fiber bundle over `B` where each fiber is a cone i.e. has
multiplicative action by `ℝ`. -/
class ConeBundle (B : outParam (Type u)) (E : Type v) extends MulAction ℝ E, FiberBundle B E where
  /-- Tip of the cone, usually zero of the tangent space. -/
  tip : B → E
  proj_tip (b : B) : proj (tip b) = b
  proj_smul (s : ℝ) (e : E) : proj (s • e) = proj e
  zero_smul (e : E) : (0:ℝ) • e = tip (proj e)
  smul_zero (s : ℝ) (b : B) : s • (tip b) = tip b
  smul_smul (s r : ℝ) (e : E) : s • r • e = (s * r) • e


attribute [simp] ConeBundle.proj_smul ConeBundle.zero_smul ConeBundle.proj_tip


open Diffeology in
/-- Tangnet bundle `TX` of `X` is a space of pair of a point `x : X` and tangent vector.
This is a generalization of tangent bundle for manifold which gives us the minimal structure to
talk about derivatives. -/
class TangentBundle (X : Type v) [Diffeology X] (TX : outParam (Type w)) extends ConeBundle X TX where

  /-- Map assigning tangent vectors to plots. -/
  tangentMap (c : ℝ^n → X) (hc : c ∈ plots n) (x dx : ℝ^n) : TX

  /-- Tangent map assigs tangent vector at the expected position. -/
  tangentMap_proj (c : ℝ^n → X) (hc : c ∈ plots n) (x dx : ℝ^n) :
    proj (tangentMap c hc x dx) = c x

  /-- Chain rule for composing with smooth function -/
  tangentMap_comp
    (c : ℝ^n → X) (hc : c ∈ plots n)
    (f : ℝ^m → ℝ^n) (hf : ContDiff ℝ ⊤ f)
    (x dx : ℝ^m) :
    tangentMap (c ∘ f) (plot_comp hc hf) x dx = tangentMap c hc (f x) (fderiv ℝ f x dx)

  /-- Tangent of constant function is zero. -/
  tangentMap_const {n} (x : X) (t dt) :
    tangentMap (fun _ : ℝ^n => x) (const_plot n x) t dt = tip x

  /-- Tangent map is linear map -/
  tangentMap_smul {n : ℕ} (p : ℝ^n → X) (hp : p ∈ plots n (X:=X)) (x dx : ℝ^n) :
    ∀ (s : ℝ), s • tangentMap p hp x dx = tangentMap p hp x (s•dx)

  /-- Canonical curve going through `xdx`. -/
  exp (xdx : TX) (t : ℝ^1) : TX
  /-- Canonical curve going through `x` does go through `xdx` -/
  exp_at_zero (xdx : TX) : exp xdx 0 = xdx

  /-- Canonical curve is a plot when projected to the base space. -/
  exp_is_plot (xdx : TX) : (fun t => proj (exp xdx t)) ∈ plots 1

  /-- Canonical curve going through `xdx` does do in direction `xdx` at zero. -/
  tangentMap_exp_at_zero (xdx : TX) :
    tangentMap (fun x => proj (exp xdx x)) (exp_is_plot xdx) 0 = fun s => (s 0) • xdx

attribute [simp]
  TangentBundle.exp_at_zero
  TangentBundle.tangentMap_const
  TangentBundle.tangentMap_exp_at_zero
  TangentBundle.tangentMap_smul

section TangentBundle

variable
  {X : Type*} {TX : Type*} [Diffeology X] [TangentBundle X TX]
  {Y : Type*} {TY : Type*} [Diffeology Y] [TangentBundle Y TY]
  {Z : Type*} {TZ : Type*} [Diffeology Z] [TangentBundle Z TZ]


open Diffeology TangentBundle in
/-- Smooth function between diffeological spaces equiped with tangent bundle.

Smooth function maps plots to plots and tangent depends only on the plot's point and tangent

NOTE: There is also `TSSmooth` which is a smooth function between diffological spaces with
      tangent space. It should be more or less equivalent definition. We have both to see
      which one is easier to work with.
-/
@[fun_prop]
structure TBSmooth (f : X → Y) extends DSmooth f : Prop where
  plot_independence {n : ℕ} {p q : ℝ^n → X} {x : ℝ^n}
    (hp : p ∈ plots n) (hq : q ∈ plots n)
    (hdx : tangentMap p hp x = tangentMap q hq x) :
    tangentMap (fun x => f (p x)) (plot_preserving _ hp) x = tangentMap (f∘q) (plot_preserving _ hq) x

namespace TBSmooth

@[fun_prop]
theorem dsmooth_rule (f : X → Y) (hf : TBSmooth f) : DSmooth f := hf.toDSmooth

@[fun_prop]
theorem id_rule : TBSmooth (fun x : X => x) := by
  constructor
  · intros; unfold Function.comp; simp_all
  · fun_prop

@[fun_prop]
theorem const_rule (y : Y) : TBSmooth (fun _ : X => y) := by
  constructor
  · intros; simp only [Function.comp_apply, Function.comp_def, cast_eq]
  · fun_prop

@[fun_prop]
theorem comp_rule (f : Y → Z) (g : X → Y)
    (hf : TBSmooth f) (hg : TBSmooth g) :
    TBSmooth (fun x => f (g x)) := by

  constructor
  case toDSmooth => fun_prop
  case plot_independence =>
    intros n p q x hp hq hdx
    have hp' := hg.plot_preserving _ hp
    have hq' := hg.plot_preserving _ hq
    exact hf.plot_independence hp' hq' (hg.plot_independence hp hq hdx)

end TBSmooth


open Classical Diffeology TangentBundle FiberBundle ConeBundle in
/-- Derivative of a function between two difeological spaces equiped with tangent bundle. -/
@[fun_trans]
noncomputable
def tbderiv (f : X → Y) (xdx : TX) : TY :=
  if h : TBSmooth f then
    let p := f ∘ proj ∘ exp X xdx
    let hp := (h.plot_preserving _ (exp_is_plot xdx))
    tangentMap p hp 0 1
  else
    tip (f (proj xdx))


namespace tbderiv

open FiberBundle ConeBundle

@[fun_trans]
theorem id_rule : tbderiv (fun x : X => x) = fun xdx => xdx := by

  have h : TBSmooth (fun x : X => x) := by fun_prop
  unfold tbderiv; simp[h, Function.comp_def]

@[fun_trans]
theorem const_rule (y : Y) : tbderiv (fun _ : X => y) = fun _ => tip y := by

  have h : TBSmooth (fun _ : X => y) := by fun_prop
  unfold tbderiv; simp[h, Function.comp_def]

open TangentBundle FiberBundle in
@[fun_trans]
theorem comp_rule (f : Y → Z) (g : X → Y)
    (hf : TBSmooth f) (hg : TBSmooth g) :
    tbderiv (fun x => f (g x))
    =
    fun xdx =>
      let ydy  := tbderiv g xdx
      tbderiv f ydy := by

  funext xdx
  have h : TBSmooth fun x => f (g x) := by fun_prop

  let ydy := tbderiv g xdx
  let p := g ∘ (proj ∘ exp X xdx)
  let q := fun t => proj (B:=Y) (exp Y ydy t)
  have hp := hg.plot_preserving _ (exp_is_plot (X:=X) xdx)
  have hq := exp_is_plot (X:=Y) ydy
  have hdx : tangentMap p hp 0 = tangentMap q hq 0 := by
    simp[p,q,ydy,tbderiv,hg,Function.comp_def]
    funext s; congr; funext r; simp[hg]; congr; aesop

  have h' := hf.plot_independence hp hq hdx
  simp [p] at h'
  conv => lhs; simp[h, hf, hg, Function.comp_def, tbderiv]; rw[h']
  simp_all [tbderiv,hf,hg,q,ydy,Function.comp_def]

end tbderiv
