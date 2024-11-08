import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.TangentSpace
-- import SciLean.Analysis.Diffeology.SumInstances

namespace SciLean

local notation:max "ℝ^" n:max => Fin n → ℝ

open Diffeology

variable {X Y : Type*} [Diffeology X] [Diffeology Y]

open Diffeology in
instance : Diffeology (Sum X Y) where
  Plot n := Plot X n ⊕ Plot Y n
  plotEval p u := p.map (fun p => p u) (fun q => q u)
  plot_ext p q h :=
    match p, q with
    | .inl p, .inl q => by
      congr; ext x; simp at h
      have h := congrFun h x
      simp_all
    | .inr p, .inr q => by
      congr; ext x; simp at h
      have h := congrFun h x
      simp_all
    | .inl _, .inr _ => by have h := congrFun h 0; simp at h;
    | .inr _, .inl _ => by have h := congrFun h 0; simp at h;
  plotComp p f hf := p.map (fun p => plotComp p hf) (fun q => plotComp q hf)
  plotComp_eval := by
    intro n m p f hf u
    cases p <;> simp
  constPlot n x := x.map (fun x => constPlot n x) (fun y => constPlot n y)
  constPlot_eval := by
    intro n x? u
    cases x? <;> simp


@[simp]
theorem SumPlot.eval_inl' (f : Plot X n) :
    DFunLike.coe (F:=Plot (Sum X Y) n) (.inl f) = fun u => .inl (f u) := by rfl

@[simp]
theorem SumPlot.eval_inr' (f : Plot Y n) :
    DFunLike.coe (F:=Plot (Sum X Y) n) (.inr f) = fun u => .inr (f u) := by rfl


@[reducible]
instance {α : Type*} {β : α → Type u} {γ : Type*} {δ : γ → Type u}
         [∀ a, AddCommGroup (β a)] [∀ c, AddCommGroup (δ c)] (ac : α ⊕ γ) : AddCommGroup (Sum.rec β δ ac) :=
  match ac with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance


@[reducible]
instance {α : Type*} {β : α → Type u} {γ : Type*} {δ : γ → Type u}
         [Semiring R]
         [∀ a, AddCommGroup (β a)] [∀ a, Module R (β a)] [∀ c, AddCommGroup (δ c)] [∀ c, Module R (δ c)] (ac : α ⊕ γ) :
         Module R (Sum.rec β δ ac) :=
  match ac with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance


def tmTranspose'
    {X : Type*} {TX : X → Type _} [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)]
    {Y : Type*} {TY : Y → Type _} [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)]
    {U : Type*} [AddCommGroup U] [Module ℝ U]:
    (Σ x, U →ₗ[ℝ] TX x) ⊕ (Σ y, U →ₗ[ℝ] TY y) ≃ Σ (xy : X⊕Y), (U →ₗ[ℝ] Sum.rec TX TY xy) where

  toFun := fun xdx => xdx.elim (fun ⟨x,dx⟩ => ⟨Sum.inl x, dx⟩) (fun ⟨y,dy⟩ => ⟨Sum.inr y, dy⟩)
  invFun := fun xdx =>
    match xdx with
    | ⟨.inl x, dx⟩ => .inl ⟨x,dx⟩
    | ⟨.inr y, dy⟩ => .inr ⟨y,dy⟩
  left_inv := by intro x; cases x <;> simp
  right_inv := by intro ⟨x,dx⟩; cases x <;> simp

def tmTranspose
    {X : Type*} {TX : X → Type _}
    {Y : Type*} {TY : Y → Type _} :
    (Σ x, TX x) ⊕ (Σ y, TY y) ≃ Σ (xy : X⊕Y), (Sum.rec TX TY xy) where

  toFun := fun xdx => xdx.elim (fun ⟨x,dx⟩ => ⟨Sum.inl x, dx⟩) (fun ⟨y,dy⟩ => ⟨Sum.inr y, dy⟩)
  invFun := fun xdx =>
    match xdx with
    | ⟨.inl x, dx⟩ => .inl ⟨x,dx⟩
    | ⟨.inr y, dy⟩ => .inr ⟨y,dy⟩
  left_inv := by intro x; cases x <;> simp
  right_inv := by intro ⟨x,dx⟩; cases x <;> simp


open TangentSpace in
instance
    {X : Type u} {TX : outParam (X → Type v)} [Diffeology X]
    [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
    {Y : Type w} {TY : outParam (Y → Type v)} [Diffeology Y]
    [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY] :
    TangentSpace (Sum X Y) (Sum.rec TX TY) where

  tangentMap {n} p u := tmTranspose' (p.map (fun p => tangentMap p u) (fun q => tangentMap q u))
  exp := fun xdx => (tmTranspose.symm xdx).map (fun xdx => exp xdx) (fun ydy => exp ydy)

  tangentMap_const := by intro n x u; cases x <;> simp[tmTranspose',constPlot]
  tangentMap_fst := by intro n x u; cases x <;> simp[tmTranspose']
  exp_at_zero := by intro ⟨x,dx⟩; cases x <;> simp[tmTranspose]
  tangentMap_exp_at_zero := by intro ⟨x,dx⟩; cases x <;> simp[tmTranspose,tmTranspose',duality]


variable
  {X : Type u} [Diffeology X] {TX : X → Type w} [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
  {Y : Type v} [Diffeology Y] {TY : Y → Type w} [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY]

open TangentSpace

@[fun_prop]
theorem Sum.inl.arg_val.DSmooth_rule :
    DSmooth (@Sum.inl X Y) := by
  existsi fun _ p => .inl p
  intros; simp

@[simp]
theorem plotMap_inl (p : Plot X n) :
  (@Sum.inl X Y) ∘ₚ p = @Sum.inl (Plot X n) (Plot Y n) p := by ext u; simp

@[fun_prop]
theorem Sum.inl.arg_val.TSSmooth_rule :
    TSSmooth (@Sum.inl X Y) := by
  constructor
  case toDSmooth => fun_prop
  case plot_independence =>
    intro n p q u h
    simp_all[tangentMap]

@[fun_prop]
theorem Sum.inr.arg_val.DSmooth_rule :
    DSmooth (@Sum.inr X Y) := by
  existsi fun _ p => .inr p
  intros; simp

@[simp]
theorem plotMap_inr (p : Plot Y n) :
  (@Sum.inr X Y) ∘ₚ p = @Sum.inr (Plot X n) (Plot Y n) p := by ext u; simp

@[fun_prop]
theorem Sum.inr.arg_val.TSSmooth_rule :
    TSSmooth (@Sum.inr X Y) := by
  constructor
  case toDSmooth => fun_prop
  case plot_independence =>
    intro n p q u h
    simp_all[tangentMap]
