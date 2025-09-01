import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.TangentSpace
import Mathlib.Logic.Lemmas

namespace SciLean

local notation:max "ℝ^" n:max => Fin n → ℝ

variable
  {X : Type*} {TX : outParam (X → Type*)} [Diffeology X] [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
  {Y : Type*} {TY : outParam (Y → Type*)} [Diffeology Y] [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY]
  {Z : Type*} {TZ : outParam (Z → Type*)} [Diffeology Z] [∀ z, AddCommGroup (TZ z)] [∀ z, Module ℝ (TZ z)] [TangentSpace Z TZ]

open Diffeology

instance : Diffeology (X × Y) where
  Plot n := Plot X n × Plot Y n
  plotEval p u := (p.1 u, p.2 u)
  plot_ext := by
    intro n (p,p') (q,q') h
    have h := fun x => congrFun h x; simp at h
    ext x <;> simp only [(h x).1, (h x).2]
  plotComp n m p {f} hf := (plotComp p.1 hf, plotComp p.2 hf)
  plotComp_eval := by simp
  constPlot n xy := (constPlot n xy.1, constPlot n xy.2)
  constPlot_eval := by simp

@[simp]
theorem prodPlot_eval (p : Plot X n) (q : Plot Y n) (u) :
    (show Plot (X×Y) n from (p, q)) u = (p u, q u) := rfl

@[simp]
theorem prodPlot_eval' (p : Plot (X×Y) n) (u) :
    p u = (p.1 u ,p.2 u) := rfl

@[simp]
theorem prodPlot_comp (p : Plot X n) (q : Plot Y n) (f : ℝ^m → ℝ^n) (hf : ContDiff ℝ ⊤ f) :
    (show Plot (X×Y) n from (p, q)).comp hf = (p.comp hf, q.comp hf) := rfl

def tmTranspose'
    {X : Type*} {TX : X → Type _} [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [Diffeology X] [TangentSpace X TX]
    {Y : Type*} {TY : Y → Type _} [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [Diffeology Y] [TangentSpace Y TY]
    {U : Type*} [AddCommGroup U] [Module ℝ U]:
    (Σ x, U →ₗ[ℝ] TX x) × (Σ y, U →ₗ[ℝ] TY y) ≃ Σ (xy : X×Y), (U →ₗ[ℝ] TX xy.1 × TY xy.2) where

  toFun := fun (⟨x,df⟩,⟨y,dg⟩) => ⟨(x,y), fun u =>ₗ[ℝ] (df u, dg u)⟩
  invFun := fun ⟨xy,dfg⟩ => (⟨xy.1, fun u =>ₗ[ℝ] (dfg u).1⟩, ⟨xy.2, fun u =>ₗ[ℝ] (dfg u).2⟩)
  left_inv := by intro ⟨⟨x,dx'⟩,⟨y,dy⟩⟩; simp; constructor <;> apply LinearMap.eta_reduce
  right_inv := by intro ⟨(x,y),dy⟩; simp; exact LinearMap.eta_reduce dy


def tmTranspose
    {X : Type*} {TX : X → Type _}
    {Y : Type*} {TY : Y → Type _} :
    (Σ x, TX x) × (Σ y, TY y) ≃ Σ (xy : X×Y), TX xy.1 × TY xy.2 where

  toFun := fun (⟨x,dx⟩,⟨y,dy⟩) => ⟨(x,y), (dx,dy)⟩
  invFun := fun ⟨xy,dxy⟩ => (⟨xy.1,dxy.1⟩, ⟨xy.2,dxy.2⟩)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

open TangentSpace in
noncomputable
instance
    {X : Type*} {TX : outParam (X → Type*)} [Diffeology X]
    {Y : Type*} {TY : outParam (Y → Type*)} [Diffeology Y]
    [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
    [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY] :
    TangentSpace (X × Y) (fun xy => TX xy.1 × TY xy.2) where

  tangentMap c x :=
    let xdx := tangentMap c.1 x
    let ydy := tangentMap c.2 x
    tmTranspose' (xdx,ydy)

  tangentMap_fst := by intro n (p,q) u; simp[tmTranspose']

  tangentMap_const := by
    intro n (x,y) t
    simp[constPlot]
    rfl

  exp xdx :=
    let (xdx,ydy) := tmTranspose.symm xdx
    (exp xdx, exp ydy)

  exp_at_zero := by intro ⟨(x,y),(dx,dy)⟩; simp[tmTranspose]

  tangentMap_exp_at_zero := by
    intro ⟨(x,y),(dx,dy)⟩
    simp[tmTranspose',tmTranspose,duality]

open TangentSpace

@[simp]
theorem plot_exp_prod (x : X) (y : Y) (dx : TX x) (dy : TY y) :
  exp ⟨(x,y),(dx,dy)⟩ = (exp ⟨x,dx⟩, exp ⟨y,dy⟩) := by rfl


@[simp]
theorem tmTranspose'_symm_tangentMap (p : Plot (X×Y) n) (u):
  tmTranspose'.symm (tangentMap p u)
  =
  (tangentMap p.1 u, tangentMap p.2 u) := by rfl


@[simp]
theorem tmTranspose_duality_tmTranspose (xy : (Σ x, ℝ^1 →ₗ[ℝ] TX x) × (Σ y, ℝ^1 →ₗ[ℝ] TY y)) :
    tmTranspose.symm (duality.symm (tmTranspose' xy)) = (duality.symm xy.1, duality.symm xy.2) := by
  cases xy;
  simp[duality]; rfl


variable
  {X : Type*} [Diffeology X] {TX : X → Type*} [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
  {Y : Type*} [Diffeology Y] {TY : Y → Type*} [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY]

open TangentSpace


@[fun_prop]
theorem Prod.fst.arg_self.DSmooth_rule : DSmooth (fun x : X×Y => x.1) := by
  constructor
  existsi (fun _ => Prod.fst)
  intro n u (p,_); simp

@[simp]
theorem plotMap_fst (p : Plot X n) (q : Plot Y n) :
    Prod.fst (β:=Y) ∘ₚ (p,q) = p := by
  ext u; simp

@[fun_prop]
theorem Prod.snd.arg_self.DSmooth_rule : DSmooth (fun x : X×Y => x.2) := by
  constructor
  existsi (fun _ => Prod.snd)
  intro n u (_,_); simp

@[simp]
theorem plotMap_snd (p : Plot X n) (q : Plot Y n) :
    Prod.snd (α:=X) ∘ₚ (p,q) = q := by
  ext u; simp


@[fun_prop]
theorem Prod.fst.arg_self.TSSmooth_rule : TSSmooth (fun x : X×Y => x.1) := by
  constructor
  case toDSmooth => fun_prop
  case plot_independence =>
    intro n (p,p') (q,q') u h
    simp_all[tangentMap]



@[fun_prop]
theorem Prod.snd.arg_self.TSSmooth_rule : TSSmooth (fun x : X×Y => x.2) := by
  constructor
  case toDSmooth => fun_prop
  case plot_independence =>
    intro n (p,p') (q,q') u h
    simp_all[tangentMap]


@[fun_prop]
theorem Prod.mk.arg_self.DSmooth_rule
    (f : X → Y) (hf : TSSmooth f)
    (g : X → Z) (hg : TSSmooth g) :
    DSmooth (fun x => (f x, g x)) := by
  existsi (fun _ p => (f ∘ₚ p, g ∘ₚ p))
  intros; simp


@[simp]
theorem plotMap_prod
    (f : X → Y) (hf : TSSmooth f)
    (g : X → Z) (hg : TSSmooth g)
    (p : Plot X n) :
    (fun x => (f x, g x)) ∘ₚ p = (f ∘ₚ p, g ∘ₚ p) := by
  ext u <;> simp


@[fun_prop]
theorem Prod.mk.arg_self.TSSmooth_rule
    (f : X → Y) (hf : TSSmooth f)
    (g : X → Z) (hg : TSSmooth g) :
    TSSmooth (fun x : X => (f x, g x)) := by
  constructor
  case toDSmooth =>
    constructor
    existsi (fun _ p => (f ∘ₚ p, g ∘ₚ p))
    intros; simp
  case plot_independence =>
    intro n p q u h
    simp (disch:=fun_prop) [tangentMap]
    constructor
    · apply hf.plot_independence h
    · apply hg.plot_independence h
