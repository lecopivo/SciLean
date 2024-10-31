import SciLean.Analysis.Scalar
import SciLean.Tactic.Autodiff

namespace SciLean

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
  tangent_const {x : X} {t dt} : tangent (fun _ : Fin n → ℝ => x) (const_plot n x) t dt = 0

  /-- Canonical curve going through `x` in direction `dx`. -/
  curve (x : X) (dx : TX x) : (Fin 1 → ℝ) → X
  curve_at_zero (x : X) (dx : TX x) : curve x dx (fun _ => 0) = x
  curve_is_plot (x : X) (dx : TX x) : curve x dx ∈ plots 1

  -- maybe replace this with the requirement that the map is linear
  -- requiring that tangent of curve is
  tangent_curve_at_zero (x : X) (dx : TX x) dt :
    tangent (curve x dx) (curve_is_plot x dx) (fun _ => 0) dt = cast (by simp_all) (dt 0 • dx)

  -- I think semilinearity is sufficient
  tangent_linear {n : ℕ} (c : (Fin n → ℝ) → X) (hc : c ∈ plots n (X:=X)) (x : (Fin n) → ℝ) :
    IsLinearMap ℝ (tangent c hc x)

attribute [simp] TangentSpace.curve_at_zero TangentSpace.tangent_curve_at_zero TangentSpace.tangent_const


variable
  {R : Type*} [RealScalar R]
  {X : Type*} {TX : X → Type*} [Diffeology X] [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
  {Y : Type*} {TY : Y → Type*} [Diffeology Y] [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY]
  {Z : Type*} {TZ : Z → Type*} [Diffeology Z] [∀ z, AddCommGroup (TZ z)] [∀ z, Module ℝ (TZ z)] [TangentSpace Z TZ]



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
  · intros; simp_all [Function.comp]
  · intros; simp_all [Function.comp]

@[fun_prop]
theorem MDifferentiable.const_rule (y : Y) : MDifferentiable (fun _ : X => y) := by
  constructor
  · intros; simp only [Function.comp_apply, Function.comp, cast_eq]
  · intros; simp only [Function.comp, Diffeology.const_plot]


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


set_option trace.Meta.Tactic.fun_prop true in
example (f : Y → Z) (g : X → Y)
    (hf : MDifferentiable f) (hg : MDifferentiable g) :
    MDifferentiable (fun x => f (g x)) := by fun_prop



theorem mderiv.id_rule :
    mderiv (fun x : X => x) = fun _ dx => dx := by

  have h : MDifferentiable (fun x : X => x) := by fun_prop
  unfold mderiv; simp[h, Function.comp]

theorem mderiv.const_rule :
    mderiv (fun _ : X => y) = fun _ _ => (0 : TY y) := by

  have h : MDifferentiable (fun _ : X => y) := by fun_prop
  unfold mderiv; simp[h, Function.comp]


@[simp]
theorem cast_apply (f : α → β) (a : α) (h' : (α → β) = (α → β')) (h : β = β' := by simp_all) :
  (cast h' f) a = cast h (f a) := by subst h; simp


@[simp]
theorem cast_smul {R M M'} [SMul R M'] (h : M = M') (r : R) (x : M) :
  have : SMul R M := by rw[h]; infer_instance
  r • cast h x = cast h (r • x) := by subst h; simp

@[fun_trans]
theorem mderiv.comp_rule (f : Y → Z) (g : X → Y)
    (hf : MDifferentiable f) (hg : MDifferentiable g) :
    mderiv (fun x => f (g x))
    =
    fun x dx =>
      let y  := g x
      let dy := mderiv g x dx
      let z  := f y
      let dz := mderiv f y dy
      dz  := by

  funext x dx
  have h : MDifferentiable fun x => f (g x) := by fun_prop -- MDifferentiable.comp_rule _ _ hf hg

  -- set up arguments to use `plot_independence` to replace
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
    sorry -- just use linearity of `tangent`
  have h' := hf.plot_independence hp hq hx hdx
  simp [p] at h'
  conv =>
    lhs
    simp[h, hf, hg, Function.comp, mderiv]
    rw[h']
  simp_all [mderiv,hf,hg,q,y,dy]




example (h : α = β) (h' : β = γ) (a : α) : cast h' (cast h a) = cast (by simp_all) a := by simp

structure Id' (α : Type u) where
  val : α

example {α β : Type} (h : α = Id' α) (a : List α) : h.symm ▸ h ▸ a = a := by
