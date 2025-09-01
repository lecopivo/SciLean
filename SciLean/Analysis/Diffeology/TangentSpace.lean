import SciLean.Tactic.Autodiff
import SciLean.Analysis.Diffeology.Basic


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

variable {X : Type v} {TX : outParam (X → Type w)}
      [∀ x, AddCommGroup (TX x)] [∀ x, outParam <| Module ℝ (TX x)]

def TangentSpace.duality : (Σ x, TX x) ≃ Σ x, (ℝ^1 →ₗ[ℝ] TX x) where
  toFun := fun ⟨x,dx⟩ => ⟨x, fun s : ℝ^1 =>ₗ[ℝ] s 0•dx⟩
  invFun := fun ⟨x,dx'⟩ => ⟨x, dx' 1⟩
  left_inv := by intro x; simp
  right_inv := by
    intro ⟨x,dx'⟩; simp
    have h : ∀ (s : ℝ) t, s • dx' t = dx' (fun i => s * t i) := by
      intro s t; rw[← dx'.map_smul]; congr
    simp[h]; ext u; simp; congr; funext x; congr; aesop


@[simp]
theorem TangentSpace.duality_zero (x : X) :
  TangentSpace.duality ⟨x,(0 : TX x)⟩ = ⟨x,0⟩ := by simp[duality]

@[simp]
theorem TangentSpace.duality_zero' (x : X) :
  TangentSpace.duality.symm ⟨x,0⟩ = ⟨x,(0 : TX x)⟩ := by simp[duality]


-- todo: theorem about mapping zerov

open TangentSpace
/-- Tangent space `TX x` of `X` at point `x`. Generalization of tangent space for manifolds to
general diffeological spaces which gives us the minimal structure to talk about derivatives.
-/
class TangentSpace (X : Type v) [Diffeology X] (TX : outParam (X → Type w))
      [∀ x, AddCommGroup (TX x)] [∀ x, outParam <| Module ℝ (TX x)] where
  /-- Map assigning tangent vectors to plots. -/
  tangentMap {n : ℕ} (p : Plot X n) (u : ℝ^n) : (x : X) × (ℝ^n →ₗ[ℝ] TX x)

  /-- Tangent of constant function is zero. -/
  tangentMap_const {n} (x : X) t : tangentMap (constPlot n x) t = ⟨x, 0⟩

  tangentMap_fst {n} (p : Plot X n) (u : ℝ^n) : (tangentMap p u).1 = p u

  /-- Canonical curve going through `x` in direction `dx`. -/
  exp (x : Σ x, TX x) : Plot X 1
  /-- Canonical curve going through `x` does go through `x` -/
  exp_at_zero (xdx : Σ x, TX x) : exp xdx 0 = xdx.1 -- TODO: remove this as it follows from `tangetMap_at_zero`
  /-- Canonical curve going through `x` in direction `dx` does do in direction `dx` -/
  tangentMap_exp_at_zero (xdx : Σ x, TX x) :
    tangentMap (exp xdx) 0 = duality xdx


attribute [simp]
  TangentSpace.exp_at_zero
  TangentSpace.tangentMap_exp_at_zero
  TangentSpace.tangentMap_const
  TangentSpace.tangentMap_fst

-- #generate_linear_map_simps TangentSpace.tangentMap_linear

variable
  {X : Type*} {TX : outParam (X → Type*)} [Diffeology X]
  [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
  {Y : Type*} {TY : outParam (Y → Type*)} [Diffeology Y]
  [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY]
  {Z : Type*} {TZ : outParam (Z → Type*)} [Diffeology Z]
  [∀ z, AddCommGroup (TZ z)] [∀ z, Module ℝ (TZ z)] [TangentSpace Z TZ]

def TangentSpace.exp' (xdx' : Σ x, ℝ^1 →ₗ[ℝ] TX x) : Plot X 1 := exp (duality.symm xdx')

open Diffeology TangentSpace


@[simp]
theorem mapPlot_id (p : Plot X n) : (fun x : X => x) ∘ₚ p = p := by ext; simp

@[simp]
theorem mapPlot_const (p : Plot X n) (y : Y) : (fun x : X => y) ∘ₚ p = constPlot n y := by ext; simp

@[simp]
theorem mapPlot_comp
    (f : Y → Z) (hf : DSmooth f)
    (g : X → Y) (hg : DSmooth g)
    (p : Plot X n) :
    (f ∘ g) ∘ₚ p = f ∘ₚ g ∘ₚ p := by ext; simp


/-- Smooth function between diffeological spaces equiped with tangent spaces.

Smooth function maps plots to plots and tangent depends only on the plot's point and tangent

NOTE: There is also `TBSmooth` which is a smooth function between diffological spaces with
      tangent bundle. It should be more or less equivalent definition. We have both to see
      which one is easier to work with.
-/
@[fun_prop]
structure TSSmooth (f : X → Y) extends DSmooth f : Prop where
  plot_independence {n : ℕ} {p q : Plot X n} {u : ℝ^n}
    (h : tangentMap p u = (tangentMap q u)) :
    (tangentMap (f ∘[toDSmooth] p) u)
    =
    (tangentMap (f ∘[toDSmooth] q) u)


open TangentSpace

@[fun_prop]
theorem dsmooth_rule (f : X → Y) (hf : TSSmooth f) : DSmooth f := hf.toDSmooth


namespace TSSmooth

@[fun_prop]
theorem id_rule : TSSmooth (fun x : X => x) := by
  constructor
  case toDSmooth => fun_prop
  case plot_independence => simp_all

@[fun_prop]
theorem const_rule (y : Y) : TSSmooth (fun _ : X => y) := by
  constructor
  case toDSmooth => fun_prop
  case plot_independence => simp_all


-- set_option pp.proofs.withType true in
@[fun_prop]
theorem comp_rule (f : Y → Z) (g : X → Y)
    (hf : TSSmooth f) (hg : TSSmooth g) :
    TSSmooth (f ∘ g) := by

  constructor
  case toDSmooth => fun_prop
  case plot_independence =>
    intros n p q u h;
    simp (disch:=fun_prop)
    apply hf.plot_independence
    apply hg.plot_independence
    assumption


end TSSmooth


open Classical Diffeology TangentSpace in
/-- Derivative of a function between two difeological spaces equiped with tangent space. -/
@[fun_trans]
noncomputable
def fwdTSDeriv (f : X → Y) (xdx : (x : X) × TX x) : (y : Y) × TY y :=
  if hf : TSSmooth f then
    duality.symm (tangentMap (f ∘ₚ (exp xdx)) 0)
  else
    ⟨f xdx.1, 0⟩


theorem fwdTSDeriv_def
    {X : Type*} [Diffeology X] {TX : X → Type*} [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
    {Y : Type*} [Diffeology Y] {TY : Y → Type*} [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY]
    {f : X → Y} (hf : TSSmooth f)  :
    fwdTSDeriv f = fun xdx => duality.symm (tangentMap (f ∘ₚ (exp xdx)) 0) := by
  unfold fwdTSDeriv
  simp[hf]


namespace tsderiv

@[fun_trans]
theorem id_rule :
    fwdTSDeriv (fun x : X => x) = fun xdx => xdx := by

  funext xdx
  have h : TSSmooth (fun x : X => x) := by fun_prop
  simp [h,fwdTSDeriv]


@[fun_trans]
theorem const_rule :
    fwdTSDeriv (fun _ : X => y) = fun _ => ⟨y,(0 : TY y)⟩ := by
  funext xdx
  have h : TSSmooth (fun _ : X => y) := by fun_prop
  simp [h,fwdTSDeriv,duality]


open TangentSpace in
@[fun_trans]
theorem comp_rule (f : Y → Z) (g : X → Y)
    (hf : TSSmooth f) (hg : TSSmooth g) :
    fwdTSDeriv (f ∘ g)
    =
    fun xdx =>
      let ydy := fwdTSDeriv g xdx
      let zdz := fwdTSDeriv f ydy
      zdz  := by

  funext xdx
  have hfg : TSSmooth (f ∘ g) := by fun_prop
  simp (disch:=fun_prop) [hfg,hf,hg,fwdTSDeriv]
  let ydy' := (tangentMap (g ∘ₚ exp xdx)) 0
  let q := exp (duality.symm ydy')
  rw[hf.plot_independence (q:=q) (h:=by simp[q])]


end tsderiv
