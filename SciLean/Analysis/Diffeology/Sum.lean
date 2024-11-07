import SciLean.Analysis.Diffeology.Basic'
import SciLean.Analysis.Diffeology.TangentSpace'
-- import SciLean.Analysis.Diffeology.SumInstances

namespace SciLean

local notation:max "ℝ^" n:max => Fin n → ℝ

open Diffeology

inductive SumPlot (X Y : Type*) [Diffeology X] [Diffeology Y] (n : ℕ) where
  | inl (p : Plot X n)
  | inr (p : Plot Y n)

variable {X Y : Type*} [Diffeology X] [Diffeology Y]

def SumPlot.eval {n} (p : SumPlot X Y n) (u : ℝ^n) : X ⊕ Y :=
  match p with
  | .inl p => .inl (p u)
  | .inr p => .inr (p u)

def SumPlot.comp {n} (p : SumPlot X Y n) {f : ℝ^m → ℝ^n} (hf : ContDiff ℝ ⊤ f) : SumPlot X Y m :=
  match p with
  | .inl p => .inl (p.comp hf)
  | .inr p => .inr (p.comp hf)

@[simp]
theorem SumPlot.eval_inl (f : Plot X n) : SumPlot.eval (.inl (Y:=Y) f) = fun u => .inl (f u) := by rfl

@[simp]
theorem SumPlot.eval_inr (f : Plot Y n) : SumPlot.eval (.inr (X:=X) f) = fun u => .inr (f u) := by rfl

@[simp]
theorem SumPlot.comp_eval (p : SumPlot X Y n) {f : ℝ^m → ℝ^n} (hf : ContDiff ℝ ⊤ f) :
   (p.comp hf).eval = fun u => p.eval (f u) := by
  funext u
  cases p <;> (simp[SumPlot.comp]; apply plotComp_eval)


open Diffeology in
instance : Diffeology (Sum X Y) where
  Plot := SumPlot X Y
  plotEval := SumPlot.eval
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
    | .inl _, .inr _ => by have h := congrFun h 0; simp[SumPlot.eval] at h;
    | .inr _, .inl _ => by have h := congrFun h 0; simp[SumPlot.eval] at h;
  plotComp := SumPlot.comp
  plotComp_eval := by
    intro n m p f hf u
    cases p <;> simp
  constPlot n x? :=
    match x? with
    | .inl x => .inl (constPlot n x)
    | .inr y => .inr (constPlot n y)
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


open TangentSpace in
instance
    {X : Type u} {TX : outParam (X → Type v)} [Diffeology X]
    [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
    {Y : Type w} {TY : outParam (Y → Type v)} [Diffeology Y]
    [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY] :
    TangentSpace (Sum X Y) (Sum.rec TX TY) where

  tangentMap {n} p u du :=
    match p with
    | .inl p => tangentMap p u du
    | .inr p => tangentMap p u du

  tangentMap_const := by
    intro n x? u du
    cases x? <;> simp

  exp x dx :=
    match x, dx with
    | .inl x, dx => .inl (exp x dx)
    | .inr y, dy => .inr (exp y dy)

  exp_at_zero := by intros x dx; cases x; simp; simp

  tangentMap_exp_at_zero x dx t :=
    match x, dx with
    | .inl x, dx => by simp
    | .inr y, dy => by simp

  tangentMap_linear := by
    intros n p u
    cases p <;> apply tangentMap_linear
