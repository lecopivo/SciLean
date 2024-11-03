import SciLean.Tactic.Autodiff
import SciLean.Data.ArrayN

import SciLean.Analysis.Diffeology.Util

namespace SciLean

open Diffeology.Util

/-- Diffeology on `X` says that which curves are differentiable. -/
class Diffeology (X : Type v) where
  plots (n : ℕ) : Set ((Fin n → ℝ) → X)
  smooth_comp {n m} {p} {f : (Fin n → ℝ) → (Fin m → ℝ)}
    (ph : p ∈ plots m) (hf : Differentiable ℝ f) : p ∘ f ∈ plots n
  const_plot (n : ℕ) (x : X) : (fun _ => x) ∈ plots n


open Diffeology in
class TangentSpace (X : Type v) [Diffeology X] (TX : outParam (X → Type w)) [∀ x, outParam <| AddCommGroup (TX x)] [∀ x, outParam <| Module ℝ (TX x)] where
  /-- Map assigning tangent vectors to plots. -/
  tangent {n : ℕ} (c : (Fin n → ℝ) → X) (hc : c ∈ plots n (X:=X)) (x dx : (Fin n) → ℝ) : TX (c x)
  /-- Chain rule for composing with differentiable function. -/
  smooth_comp {n m} {p} {f : (Fin n → ℝ) → (Fin m → ℝ)}
    (hp : p ∈ plots m) (hf : Differentiable ℝ f) (x dx) :
    tangent (p∘f) (smooth_comp hp hf) x dx = tangent p hp (f x) (fderiv ℝ f x dx)
  /-- Tangent of constant function is zero. -/
  tangent_const {n} (x : X) (t dt) : tangent (fun _ : Fin n → ℝ => x) (const_plot n x) t dt = 0

  /-- Canonical curve going through `x` in direction `dx`. -/
  curve (x : X) (dx : TX x) : (Fin 1 → ℝ) → X
  curve_at_zero (x : X) (dx : TX x) : curve x dx (no_index (fun _ => 0)) = x
  curve_is_plot (x : X) (dx : TX x) : curve x dx ∈ plots 1

  -- maybe replace this with the requirement that the map is linear
  -- requiring that tangent of curve is
  tangent_curve_at_zero (x : X) (dx : TX x) dt :
    tangent (curve x dx) (curve_is_plot x dx) (fun _ => 0) dt = dt 0 • cast (by simp_all) dx

  -- I think semilinearity is sufficient
  tangent_linear {n : ℕ} (c : (Fin n → ℝ) → X) (hc : c ∈ plots n (X:=X)) (x : (Fin n) → ℝ) :
    IsLinearMap ℝ (tangent c hc x)


attribute [simp] TangentSpace.curve_at_zero TangentSpace.tangent_curve_at_zero TangentSpace.tangent_const

variable
  {X : Type*} {TX : outParam (X → Type*)} [Diffeology X] [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
  {Y : Type*} {TY : outParam (Y → Type*)} [Diffeology Y] [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY]
  {Z : Type*} {TZ : outParam (Z → Type*)} [Diffeology Z] [∀ z, AddCommGroup (TZ z)] [∀ z, Module ℝ (TZ z)] [TangentSpace Z TZ]



open Diffeology TangentSpace in
@[fun_prop]
structure MDifferentiable (f : X → Y) : Prop where
  plot_preserving :
    ∀ {n : ℕ}, ∀ px ∈ plots n, f ∘ px ∈ plots n
  plot_independence {n : ℕ} {p q : (Fin n → ℝ) → X} {x : Fin n → ℝ}
    (hp : p ∈ plots n) (hq : q ∈ plots n)
    (hx : p x = q x) (hdx : tangent p hp x = cast (by simp_all) (tangent q hq x)) :
    tangent (fun x => f (p x)) (plot_preserving _ hp) x = cast (by simp[hx]) (tangent (f∘q) (plot_preserving _ hq) x)


open Classical Diffeology TangentSpace in
@[fun_trans]
noncomputable
def mderiv (f : X → Y) (x : X) (dx : TX x) : TY (f x) :=
  if h : MDifferentiable f then
    cast (by simp_all) (tangent (f∘curve x dx) (h.plot_preserving _ (curve_is_plot x dx)) (fun _ => 0) (fun _ => 1))
  else
    (0 : TY (f x))


@[fun_prop]
theorem MDifferentiable.id_rule : MDifferentiable (fun x : X => x) := by
  constructor
  · intros; unfold Function.comp; simp_all
  · intros; unfold Function.comp; simp_all

@[fun_prop]
theorem MDifferentiable.const_rule (y : Y) : MDifferentiable (fun _ : X => y) := by
  constructor
  · intros; simp only [Function.comp_apply, Function.comp_def, cast_eq]
  · intros; simp only [Function.comp_def, Diffeology.const_plot]


@[fun_prop]
theorem MDifferentiable.comp_rule (f : Y → Z) (g : X → Y)
    (hf : MDifferentiable f) (hg : MDifferentiable g) :
    MDifferentiable (fun x => f (g x)) := by

  constructor
  case plot_preserving =>
    intros n p hp;
    exact hf.plot_preserving _ (hg.plot_preserving _ hp)
  case plot_independence =>
    intros n p q x hp hq hx hdx
    let hp' := hg.plot_preserving _ hp
    let hq' := hg.plot_preserving _ hq
    exact hf.plot_independence hp' hq' (by simp_all) (hg.plot_independence hp hq hx hdx)

@[fun_trans]
theorem mderiv.id_rule :
    mderiv (fun x : X => x) = fun _ dx => dx := by

  have h : MDifferentiable (fun x : X => x) := by fun_prop
  unfold mderiv; simp[h, Function.comp_def]

@[fun_trans]
theorem mderiv.const_rule :
    mderiv (fun _ : X => y) = fun _ _ => (0 : TY y) := by

  have h : MDifferentiable (fun _ : X => y) := by fun_prop
  unfold mderiv; simp[h, Function.comp_def]


@[fun_trans]
theorem mderiv.comp_rule (f : Y → Z) (g : X → Y)
    (hf : MDifferentiable f) (hg : MDifferentiable g) :
    mderiv (fun x => f (g x))
    =
    fun x dx =>
      let y  := g x
      let dy := mderiv g x dx
      let dz := mderiv f y dy
      dz  := by

  funext x dx
  have h : MDifferentiable fun x => f (g x) := by fun_prop -- MDifferentiable.comp_rule _ _ hf hg

  -- set up arguments to use `plot_independence`
  let y  := g x
  let dy := mderiv g x dx
  let p := g ∘ (TangentSpace.curve x dx)
  let hp : p ∈ Diffeology.plots 1 := hg.plot_preserving _ (TangentSpace.curve_is_plot x dx)
  let q  := TangentSpace.curve y dy
  let hq : q ∈ Diffeology.plots 1 := TangentSpace.curve_is_plot y dy
  let t := (fun _ : Fin 1 => (0 : ℝ))
  have hx : p t = q t := by simp[p,q,t]
  open TangentSpace in
  have hdx : tangent p hp t = cast (by simp[hx]) (tangent q hq t) := by
    funext dt
    simp [p,q,tangent_curve_at_zero,t,dy,mderiv,hg]
    have h := (TangentSpace.tangent_linear p hp (fun _ => 0)).map_smul (dt 0) (fun _ => 1) |>.symm
    simp[h]; congr; funext x; simp; congr; ext; simp only [Fin.val_eq_zero, Fin.isValue]

  -- use `plot_independence`
  have h' := hf.plot_independence hp hq hx hdx

  -- now just unfold definitions, use `h'` and we are done
  simp [p] at h'
  conv => lhs; simp[h, hf, hg, Function.comp_def, mderiv]; rw[h']
  simp_all [mderiv,hf,hg,q,y,dy]


class FiberBundle (B : Type u) (E : Type v) where
  proj : E → B

open FiberBundle in
class ConeBundle (B : Type u) (E : Type v) extends MulAction ℝ E, FiberBundle B E where
  tip : B → E
  proj_smul (s : ℝ) (e : E) : proj (s • e) = proj e
  smul_zero (e : E) : (0:ℝ) • e = tip (proj e)
  proj_tip (b : B) : proj (tip b) = b

attribute [simp] ConeBundle.proj_smul ConeBundle.smul_zero ConeBundle.proj_tip


open Diffeology in
class TangentBundle (X : Type v) [Diffeology X] (TX : outParam (Type w)) extends ConeBundle X TX where

  tangentMap (c : (Fin n → ℝ) → X) (hc : c ∈ plots n) (x dx : (Fin n) → ℝ) : TX

  tangentMap_proj (c : (Fin n → ℝ) → X) (hc : c ∈ plots n) (x dx : (Fin n) → ℝ) :
    proj (tangentMap c hc x dx) = c x

  tangentMap_comp
    (c : (Fin n → ℝ) → X) (hc : c ∈ plots n)
    (f : (Fin m → ℝ) → (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (x dx : (Fin m) → ℝ) :
    tangentMap (c ∘ f) (smooth_comp hc hf) x dx = tangentMap c hc (f x) (fderiv ℝ f x dx)

  smul_tangentMap (c : (Fin n → ℝ) → X) (hc : c ∈ plots n) (x dx : (Fin n) → ℝ) (s : ℝ) :
    s • (tangentMap c hc x dx) = tangentMap c hc x (s • dx)

  exp (xdx : TX) (t : Fin 1 → ℝ) : TX

  exp_plot (xdx : TX) : (fun t => proj (exp xdx t)) ∈ plots 1

  exp_at_zero (xdx : TX) :
    exp xdx 0 = xdx

  tangentMap_const (x : X)
    : tangentMap (fun _ : (Fin n → ℝ) => x) (const_plot n x) = fun _ _ => tip x

  tangentMap_exp (xdx : TX) :
    tangentMap (fun x => proj (exp xdx x)) (exp_plot xdx) (fun _ => 0) = fun s => (s 0) • xdx

attribute [simp] TangentBundle.exp_at_zero TangentBundle.tangentMap_const TangentBundle.tangentMap_exp TangentBundle.smul_tangentMap

section TangentBundle

variable
  {X : Type*} {TX : Type*} [Diffeology X] [TangentBundle X TX]
  {Y : Type*} {TY : Type*} [Diffeology Y] [TangentBundle Y TY]
  {Z : Type*} {TZ : Type*} [Diffeology Z] [TangentBundle Z TZ]


open Diffeology TangentBundle in
@[fun_prop]
structure TDifferentiable (f : X → Y) : Prop where
  plot_preserving :
    ∀ {n : ℕ}, ∀ px ∈ plots n, f ∘ px ∈ plots n
  plot_independence {n : ℕ} {p q : (Fin n → ℝ) → X} {x : Fin n → ℝ}
    (hp : p ∈ plots n) (hq : q ∈ plots n)
    (hdx : tangentMap p hp x = tangentMap q hq x) :
    tangentMap (fun x => f (p x)) (plot_preserving _ hp) x = tangentMap (f∘q) (plot_preserving _ hq) x


open Classical Diffeology TangentBundle FiberBundle ConeBundle in
@[fun_trans]
noncomputable
def tderiv (f : X → Y) (xdx : TX) : TY :=
  if h : TDifferentiable f then
    tangentMap (f∘(fun t => proj (exp X xdx t))) (h.plot_preserving _ (exp_plot _)) (fun _ => 0) (fun _ => 1)
  else
    tip (f (proj xdx))


@[fun_prop]
theorem TDifferentiable.id_rule : TDifferentiable (fun x : X => x) := by
  constructor
  · intros; unfold Function.comp; simp_all
  · intros; unfold Function.comp; simp_all

@[fun_prop]
theorem TDifferentiable.const_rule (y : Y) : TDifferentiable (fun _ : X => y) := by
  constructor
  · intros; simp only [Function.comp_apply, Function.comp_def, cast_eq]
  · intros; simp only [Function.comp_def, Diffeology.const_plot]


@[fun_prop]
theorem TDifferentiable.comp_rule (f : Y → Z) (g : X → Y)
    (hf : TDifferentiable f) (hg : TDifferentiable g) :
    TDifferentiable (fun x => f (g x)) := by

  constructor
  case plot_preserving =>
    intros n p hp;
    exact hf.plot_preserving _ (hg.plot_preserving _ hp)
  case plot_independence =>
    intros n p q x hp hq hdx
    have hp' := hg.plot_preserving _ hp
    have hq' := hg.plot_preserving _ hq
    exact hf.plot_independence hp' hq' (hg.plot_independence hp hq hdx)

@[fun_trans]
theorem tderiv.id_rule :
    tderiv (fun x : X => x) = fun xdx => xdx := by

  have h : TDifferentiable (fun x : X => x) := by fun_prop
  unfold tderiv; simp[h, Function.comp_def]

@[fun_trans]
theorem tderiv.const_rule (y : Y) :
    tderiv (fun _ : X => y) = fun _ => ConeBundle.tip y := by

  have h : TDifferentiable (fun _ : X => y) := by fun_prop
  unfold tderiv; simp[h, Function.comp_def]

open TangentBundle FiberBundle in
@[fun_trans]
theorem tderiv.comp_rule (f : Y → Z) (g : X → Y)
    (hf : TDifferentiable f) (hg : TDifferentiable g) :
    tderiv (fun x => f (g x))
    =
    fun xdx =>
      let ydy  := tderiv g xdx
      tderiv f ydy := by

  funext xdx
  have h : TDifferentiable fun x => f (g x) := by fun_prop

  let ydy := tderiv g xdx
  let p := g ∘ (proj ∘ exp X xdx)
  let q := fun t => proj (B:=Y) (exp Y ydy t)
  have hp := hg.plot_preserving _ (exp_plot (X:=X) xdx)
  have hq := exp_plot (X:=Y) ydy
  let t := fun _ : Fin 1 => (0:ℝ)
  have hdx : tangentMap p hp t = tangentMap q hq t := by
    simp[p,q,t,ydy,tderiv,hg,Function.comp_def]
    funext s; congr; funext i; simp; congr; aesop

  have h' := hf.plot_independence hp hq hdx
  simp [p] at h'
  conv => lhs; simp[h, hf, hg, Function.comp_def, tderiv]; rw[h']
  simp_all [mderiv,hf,hg,q,ydy,Function.comp_def,tderiv]


end TangentBundle
