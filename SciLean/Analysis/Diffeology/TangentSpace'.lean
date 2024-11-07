import SciLean.Tactic.Autodiff
import SciLean.Data.ArrayN
import SciLean.Tactic.InferVar

import SciLean.Analysis.Diffeology.Basic'


/-!

# Tangent space of diffeological space and derivative map

Tangent space of diffeological space. It allows us to talk about derivative as a function between
two tangent spaces.


NOTE: We also define separete notion of `TangentBundle` which should be equivalent to `TangentSpace`
      - for `TX : X → Type` and `TangentSpace X TX` we have `TangentBundle X (Σ x, TX x)`
      - for `TX : Type` and `TangentBundle X TX` we have `TangentSpace X (fun x => {dx : TX // π dx = x})`
      We have both definitions to figure out which one is easier to work with.


TODO: The paper 'Tangent spaces and tangent bundles for diffeological spaces'[1]  defines internal
      and external notion of tangent space. Figure out if our definition relates to theirs.

      [1] https://arxiv.org/abs/1411.5425
-/


namespace SciLean

open Diffeology Util

local notation:max "ℝ^" n:max => (Fin n) → ℝ


/-- Tangent space `TX x` of `X` at point `x`. Generalization of tangent space for manifolds to
general diffeological spaces which gives us the minimal structure to talk about derivatives.
-/
class TangentSpace (X : Type v) [Diffeology X] (TX : outParam (X → Type w))
      [∀ x, AddCommGroup (TX x)] [∀ x, outParam <| Module ℝ (TX x)] where
  /-- Map assigning tangent vectors to plots. -/
  tangentMap {n : ℕ} (c : Plot X n) (x dx : ℝ^n) : TX (c x)

  -- NOTE: This does not seems to be necessary at it is included in the definition of differentiable
  --       function
  -- /-- Chain rule for composing with smooth function. -/
  -- tangentMap_comp {n m} {p} {f : ℝ^n → ℝ^m}
  --   (hp : p ∈ plots m) (hf : ContDiff ℝ ⊤ f) (x dx) :
  --   tangentMap (p∘f) x dx = tangentMap p (f x) (fderiv ℝ f x dx)

  /-- Tangent of constant function is zero. -/
  tangentMap_const {n} (x : X) (t dt) : tangentMap (constPlot n x) t dt = 0

  /-- Tangent map is linear map -/
  tangentMap_linear {n : ℕ} (p : Plot X n) (x : ℝ^n) :
    IsLinearMap ℝ (tangentMap p x)

  /-- Canonical curve going through `x` in direction `dx`. -/
  exp (x : X) (dx : TX x) : Plot X 1
  /-- Canonical curve going through `x` does go through `x` -/
  exp_at_zero (x : X) (dx : TX x) : exp x dx 0 = x
  /-- Canonical curve going through `x` in direction `dx` does do in direction `dx` -/
  tangentMap_exp_at_zero (x : X) (dx : TX x) dt :
    tangentMap (exp x dx) 0 dt = dt 0 • cast (by rw[exp_at_zero]) dx


attribute [simp]
  TangentSpace.exp_at_zero
  TangentSpace.tangentMap_exp_at_zero
  TangentSpace.tangentMap_const

variable
  {X : Type*} {TX : outParam (X → Type*)} [Diffeology X]
  [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
  {Y : Type*} {TY : outParam (Y → Type*)} [Diffeology Y]
  [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY]
  {Z : Type*} {TZ : outParam (Z → Type*)} [Diffeology Z]
  [∀ z, AddCommGroup (TZ z)] [∀ z, Module ℝ (TZ z)] [TangentSpace Z TZ]



open Diffeology TangentSpace in
/-- Smooth function between diffeological spaces equiped with tangent spaces.

Smooth function maps plots to plots and tangent depends only on the plot's point and tangent

NOTE: There is also `TBSmooth` which is a smooth function between diffological spaces with
      tangent bundle. It should be more or less equivalent definition. We have both to see
      which one is easier to work with.
-/
@[fun_prop]
structure TSSmooth (f : X → Y) extends DSmooth f : Prop where
  plot_independence {n : ℕ} {p q : Plot X n} {u : ℝ^n}
    (hx : p u = q u) (hdx : tangentMap p u = cast (by rw[hx]) (tangentMap q u)) :
    (tangentMap (toDSmooth.comp p) u)
    =
    (tangentMap (toDSmooth.comp q) u)


open TangentSpace
variable {n : ℕ} {p q : Plot X n} {x : ℝ^n}
    (hx : p x = q x) (hdx : tangentMap p x = cast (by rw[hx]) (tangentMap q x))
    (f : X → Y) (hf : DSmooth f)


theorem tangentMap_congr {p q : Plot X n} (h : q = p := by simp; infer_var) :
  tangentMap p u du = cast (by simp[h]) (tangentMap q u du) := by subst h; simp

@[fun_prop]
theorem dsmooth_rule (f : X → Y) (hf : TSSmooth f) : DSmooth f := hf.toDSmooth

@[simp]
theorem DSmooth.id_comp (id : DSmooth (fun x : X => x)) (p : Plot X n) :
  id.comp p = p := sorry

@[simp]
theorem DSmooth.const_comp (const : DSmooth (fun x : X => (y : Y))) (p : Plot X n) :
  const.comp p = constPlot n y  := sorry

namespace TSSmooth

@[fun_prop]
theorem id_rule : TSSmooth (fun x : X => x) := by
  constructor
  case toDSmooth => fun_prop
  case plot_independence =>
    intros;
    conv => lhs; enter[du]; rw[tangentMap_congr (h:=by simp; infer_var)]
    conv => rhs; enter[du]; rw[tangentMap_congr (h:=by simp; infer_var)]
    simp_all

@[fun_prop]
theorem const_rule (y : Y) : TSSmooth (fun _ : X => y) := by
  constructor
  case toDSmooth => fun_prop
  case plot_independence =>
    intros;
    conv => enter[1,du]; rw[tangentMap_congr (h:=by simp; infer_var)]
    conv => enter[2,du]; rw[tangentMap_congr (h:=by simp; infer_var)]

set_option pp.proofs.withType true in
@[fun_prop]
theorem comp_rule (f : Y → Z) (g : X → Y)
    (hf : TSSmooth f) (hg : TSSmooth g) :
    TSSmooth (fun x => f (g x)) := by

  constructor
  case toDSmooth => fun_prop
  case plot_independence =>
    intros n p q u hx hdx;
    let p' := hg.comp p
    let q' := hg.comp q
    have hfg : DSmooth (fun x => (f (g x))) := by fun_prop
    have hp' : hfg.comp p = hf.comp p' := by ext; simp[p']
    have hq' : hfg.comp q = hf.comp q' := by ext; simp[q']
    conv => enter[1,du]; rw[tangentMap_congr (h:=by rw[hp'])]
    conv => enter[2,du]; rw[tangentMap_congr (h:=by rw[hq'])]
    simp [p',q']
    apply hf.plot_independence (by simp_all)
    apply hg.plot_independence hx hdx

end TSSmooth


open Classical Diffeology TangentSpace in
/-- Derivative of a function between two difeological spaces equiped with tangent space. -/
@[fun_trans]
noncomputable
def tsderiv (f : X → Y) (x : X) (dx : TX x) : TY (f x) :=
  if hf : TSSmooth f then
    let p := hf.comp (exp x dx)
    let dy := tangentMap p 0 1
    cast (by simp_all[p]) dy
  else
    (0 : TY (f x))


namespace tsderiv

@[fun_trans]
theorem id_rule :
    tsderiv (fun x : X => x) = fun _ dx => dx := by

  funext x dx
  have h : TSSmooth (fun x : X => x) := by fun_prop
  unfold tsderiv
  simp[h];
  rw[tangentMap_congr (h:=by simp; infer_var)]
  simp



@[fun_trans]
theorem const_rule :
    tsderiv (fun _ : X => y) = fun _ _ => (0 : TY y) := by
  funext x dx
  have h : TSSmooth (fun _ : X => y) := by fun_prop
  unfold tsderiv
  simp[h];
  rw[tangentMap_congr (h:=by simp; infer_var)]
  simp
  sorry


open TangentSpace in
@[fun_trans]
theorem comp_rule (f : Y → Z) (g : X → Y)
    (hf : TSSmooth f) (hg : TSSmooth g) :
    tsderiv (fun x => f (g x))
    =
    fun x dx =>
      let y  := g x
      let dy := tsderiv g x dx
      let dz := tsderiv f y dy
      dz  := by

  funext x dx
  have h : TSSmooth fun x => f (g x) := by fun_prop -- TSSmooth.comp_rule _ _ hf hg

  -- set up arguments to use `plot_independence`
  let y  := g x
  let dy := tsderiv g x dx
  let p := hg.comp (exp x dx)
  let q  := exp y dy
  have hx : p 0 = q 0 := by simp[p,q]
  have hdx : tangentMap p 0 = cast (by simp[hx]) (tangentMap q 0) := by
    funext dt
    simp [p,q,tangentMap_exp_at_zero,dy,tsderiv,hg]
    have h := (tangentMap_linear p 0).map_smul (dt 0) 1 |>.symm
    simp[h]; congr; funext x; simp; congr; ext; simp only [Fin.val_eq_zero, Fin.isValue]

  -- use `plot_independence`
  have h' := hf.plot_independence hx hdx
  have hfg : TSSmooth (fun x => f (g x)) := by fun_prop
  have h'' : hfg.comp (exp x dx) = hf.comp (hg.comp (exp x dx)) := by ext; simp

  -- now just unfold definitions, use `h'` and we are done
  simp [p] at h'
  conv =>
    lhs; simp[h, hf, hg, Function.comp_def, tsderiv];
    rw[tangentMap_congr (h:=by rw[h''])]
    rw[h']
  simp (config:={zetaDelta:=true}) [q,y,dy,hf,hg,tsderiv]

end tsderiv
