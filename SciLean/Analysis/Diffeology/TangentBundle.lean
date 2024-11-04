import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.DiffeologyMap

namespace SciLean


variable
  {X : Type*} {TX : outParam (X → Type*)} [Diffeology X]
  [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
  {Y : Type*} {TY : outParam (Y → Type*)} [Diffeology Y]
  [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY]
  {Z : Type*} {TZ : outParam (Z → Type*)} [Diffeology Z]
  [∀ z, AddCommGroup (TZ z)] [∀ z, Module ℝ (TZ z)] [TangentSpace Z TZ]



class FiberBundle (B : outParam (Type u)) (E : Type v) where
  proj : E → B

open FiberBundle in
class ConeBundle (B : outParam (Type u)) (E : Type v) extends MulAction ℝ E, FiberBundle B E where
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
  simp_all [tsderiv,hf,hg,q,ydy,Function.comp_def,tderiv]

end TangentBundle

variable [Diffeology ℝ] [TangentSpace ℝ (fun _ => ℝ)]
class FiberBundle (TX : (x : X) → Type*) [∀ x, Diffeology (TX x)]
    [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [∀ x, TangentSpace (TX x) (fun _ => (TX x))]
    where
  lift : (c : DiffeologyMap ℝ X) → (s : ℝ) → (v : TX (c s)) → (t : ℝ) → TX (c.1 t)

  lift_inv (c : DiffeologyMap ℝ X) (s : ℝ) (v : TX (c s)) (t : ℝ) :
    lift c t (lift c s v t) s = v

  lift_trans (c : DiffeologyMap ℝ X) (s : ℝ) (v : TX (c s)) (t t' : ℝ) :
    lift c t (lift c s v t) t' = lift c s v t'


class FiberBundle' (E : Type u) (B : Type v)
    [Diffeology E] {TE} [∀ e, AddCommGroup (TE e)] [∀ e, Module ℝ (TE e)] [TangentSpace E TE]
    [Diffeology B] {TB} [∀ b, AddCommGroup (TB b)] [∀ b, Module ℝ (TB b)] [TangentSpace B TB]
    where
  proj : DiffeologyMap E B
  lift (c : DiffeologyMap ℝ B) (s : ℝ) (e : E) (he : proj e = b) : DiffeologyMap ℝ E


variable [Diffeology ℝ] [TangentSpace ℝ (fun _ => ℝ)]
class TangentBundle (TX : (x : X) → Type*) [∀ x, Diffeology (TX x)]
    [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [∀ x, TangentSpace (TX x) (fun _ => (TX x))]
    where
  lift : (c : DiffeologyMap ℝ X) → (s : ℝ) → (v : TX (c s)) → (t : ℝ) → TX (c.1 t)

  lift_inv (c : DiffeologyMap ℝ X) (s : ℝ) (v : TX (c s)) (t : ℝ) :
    lift c t (lift c s v t) s = v

  lift_trans (c : DiffeologyMap ℝ X) (s : ℝ) (v : TX (c s)) (t t' : ℝ) :
    lift c t (lift c s v t) t' = lift c s v t'

  -- lift_shift (c : DiffeologyMap ℝ X) (s : ℝ) (v : TX (c.1 s)) (t h : ℝ) :
  --   lift c s v t = cast (by simp) (lift ⟨fun t => c.1 (t+h), sorry⟩ (s-h) (cast (by simp) v) (t-h))


variable
    [∀ x, Diffeology (TX x)] [∀ x, TangentSpace (TX x) (fun _ => (TX x))] [TangentBundle TX]
    [∀ y, Diffeology (TY y)] [∀ y, TangentSpace (TY y) (fun _ => (TY y))] [TangentBundle TY]


variable
  {E : X → Type*} {TE : (x : X) → E x → Type*} [Diffeology (Sigma E)]
  [∀ x e, AddCommGroup (TE x e)] [∀ x e, Module ℝ (TE x e)] [TangentSpace (Sigma E) (fun p => TX p.1 × TE p.1 p.2)]


def covDeriv (f : (x : X) → E x) (x : X) (dx : TX x) : TE _ (f x)  :=
  let c := TangentSpace.curve x dx
  let c' := fun x => f (c x)
  let c' : DiffeologyMap (Fin 1 → ℝ) (Sigma E) := ⟨fun t => ⟨c t, f (c t)⟩, sorry⟩
  let v'' := TangentSpace.tangent c' sorry (fun _ => 0) (fun _ => 1)
  cast (by simp[c',c]; rw[TangentSpace.curve_at_zero]) v''.2
