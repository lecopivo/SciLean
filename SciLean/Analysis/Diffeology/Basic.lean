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




#exit

instance
    {X : Type*} {TX : X → Type*} [Diffeology X]
    {Y : Type*} {TY : Y → Type*} [Diffeology Y]
    [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
    [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY] :
    TangentSpace (DiffeologyMap X Y) (fun f => (x : X) → (TY (f.1 x))) where
  -- {n : ℕ} (c : (Fin n → ℝ) → X) (hc : c ∈ plots n (X:=X)) (x dx : (Fin n) → ℝ) : TX (c x)
  tangent {n} c hc u du x :=
    let q := fun _ : Fin 0 => x
    let hq := Diffeology.const_plot 0 x
    let p := fun u' => c u' x
    let hp : p ∈ Diffeology.plots n := hc 0 _ hq
    TangentSpace.tangent p hp u du

  smooth_comp := sorry_proof

  tangent_const := by intros; funext x; simp

  curve f df t := fun x => TangentSpace.curve (f x) (df x) t
  curve_at_zero := by intros; simp
  curve_is_plot := by simp_all[Diffeology.plots]; intros f df x; simp
