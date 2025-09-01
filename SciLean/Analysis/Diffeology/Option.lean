import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.TangentSpace
import SciLean.Analysis.Diffeology.OptionInstances

namespace SciLean

local notation:max "ℝ^" n:max => Fin n → ℝ

open Diffeology


variable {X : Type*} [Diffeology X]


open Diffeology in
instance : Diffeology (Option X) where
  Plot n := Option (Plot X n)
  plotEval := fun p u => p.map (fun p => p u)
  plot_ext p q h :=
    match p, q with
    | .none, .none => by rfl
    | .some p, .some q => by
      congr; ext x; simp at h
      have h := congrFun h x
      simp_all
    | .none, .some q => by have h := congrFun h 0; simp at h
    | .some p, .none => by have h := congrFun h 0; simp at h
  plotComp p f hf := p.map (fun p => plotComp p hf)
  plotComp_eval := by
    intro n m p f hf u
    cases p <;> simp
  constPlot n x? :=
    match x? with
    | .none => .none
    | .some x => .some (constPlot n x)
  constPlot_eval := by
    intro n x? u
    cases x? <;> simp


@[simp]
theorem OptionPlot.eval_none' :
    DFunLike.coe (F:=Plot (Option X) n) .none = fun _ => .none := by rfl

@[simp]
theorem OptionPlot.eval_some' (f : Plot X n) :
    DFunLike.coe (F:=Plot (Option X) n) (.some f) = fun x => .some (f x) := by rfl

@[simp]
theorem OptionPlot.constPlot_some (x : X) :
    constPlot (X:=Option X) n (.some x) = .some (constPlot n x)  := by rfl

@[simp]
theorem OptionPlot.constPlot_none :
    constPlot (X:=Option X) n .none = .none := by rfl


variable
    {X : Type*} {TX : outParam (X → Type*)} [Diffeology X]
    [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
    {U : Type*} [AddCommGroup U] [Module ℝ U]

def tsOptionMap' : Option (Σ x, U →ₗ[ℝ] TX x) ≃ (Σ x : Option X, U →ₗ[ℝ] Option.rec PUnit TX x) where
  invFun := fun ⟨x,dx⟩ =>
    match x, dx with
    | .none, _ => .none
    | .some x, dx => .some ⟨x,dx⟩

  toFun := fun xdx =>
    match xdx with
    | .none => ⟨.none, 0⟩
    | .some ⟨x,dx⟩ => ⟨.some x,dx⟩
  right_inv := by intro ⟨x,dx⟩; cases x; simp; rfl; simp
  left_inv := by intro x; cases x <;> simp


def tsOptionMap : Option (Σ x, TX x) ≃ (Σ x : Option X, Option.rec PUnit TX x) where
  invFun := fun ⟨x,dx⟩ =>
    match x, dx with
    | .none, _ => .none
    | .some x, dx => .some ⟨x,dx⟩

  toFun := fun xdx =>
    match xdx with
    | .none => ⟨.none, 0⟩
    | .some ⟨x,dx⟩ => ⟨.some x,dx⟩
  right_inv := by intro ⟨x,dx⟩; cases x; simp; rfl
  left_inv := by intro x; cases x <;> simp

open TangentSpace

omit [Diffeology X] [TangentSpace X TX] in
@[simp]
theorem tsOptionMap_symm_duality_symm_tsOptionMap'_some
    (xdx : (Σ x, ℝ^1 →ₗ[ℝ] TX x)) :
    tsOptionMap.symm (duality.symm (tsOptionMap' (some xdx)))
    =
    duality.symm xdx := by rfl

omit [Diffeology X] [TangentSpace X TX] in
@[simp]
theorem tsOptionMap_symm_duality_symm_tsOptionMap'_none :
    tsOptionMap.symm (duality.symm (tsOptionMap' (Option.none (α:=(Σ x, ℝ^1 →ₗ[ℝ] TX x)))))
    =
    none := by rfl

omit [Diffeology X] [(x : X) → AddCommGroup (TX x)] [(x : X) → Module ℝ (TX x)] [TangentSpace X TX] in
@[simp]
theorem tsOptionMap_symm_some (x : X) (dx : TX x) :
  tsOptionMap.symm ⟨some x, dx⟩ = some ⟨x,dx⟩ := by rfl

omit [Diffeology X] [(x : X) → AddCommGroup (TX x)] [(x : X) → Module ℝ (TX x)] [TangentSpace X TX] in
@[simp]
theorem tsOptionMap_symm_none (dx) :
  (tsOptionMap (X:=X) (TX:=TX)).symm ⟨none, dx⟩ = none := by rfl


open Classical in
noncomputable
instance
    {X : Type*} {TX : outParam (X → Type*)} [Diffeology X]
    [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX] :
    TangentSpace (Option X) (Option.rec PUnit TX) where

  tangentMap {n} p u :=
    p |>.map (tangentMap · u)
      |> tsOptionMap'

  tangentMap_const := by
    intro n x t; cases x <;> simp[tsOptionMap']
  tangentMap_fst := by
    intro n x u; cases x <;> simp[tsOptionMap']

  exp xdx :=
    tsOptionMap'.symm (duality xdx) |>.map (fun xdx' => exp (duality.symm xdx'))
  exp_at_zero := by
    intro ⟨x,dx⟩
    cases x <;> simp[tsOptionMap',duality]
  tangentMap_exp_at_zero := by
    intro ⟨x,dx⟩
    cases x <;> simp[tsOptionMap',duality]

@[fun_prop]
theorem Option.some.arg_val.DSmooth_rule :
    DSmooth (fun x : X => some x) := by
  existsi fun _ p => some p
  intros; simp

@[simp]
theorem plotMap_none (p : Plot X n) :
  (fun _ : X => none (α:=X)) ∘ₚ p = none := by ext u; simp

@[simp]
theorem plotMap_some (p : Plot X n) :
  (fun x : X => some x) ∘ₚ p = some p := by ext u; simp

open TangentSpace
@[fun_prop]
theorem Option.some.arg_val.TSSmooth_rule :
    TSSmooth (fun x : X => some x) := by

  constructor
  case toDSmooth => fun_prop
  case plot_independence =>
    intro n p q u h
    simp_all[tangentMap]
