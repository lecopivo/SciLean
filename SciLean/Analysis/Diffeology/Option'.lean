import SciLean.Analysis.Diffeology.Basic'
import SciLean.Analysis.Diffeology.TangentSpace'
import SciLean.Analysis.Diffeology.OptionInstances

namespace SciLean

local notation:max "ℝ^" n:max => Fin n → ℝ

open Diffeology

inductive OptionPlot (X : Type*) [Diffeology X] (n : ℕ) where
  | none
  | some (p : Plot X n)

variable {X : Type*} [Diffeology X]

def OptionPlot.eval {n} (p : OptionPlot X n) (u : ℝ^n) : Option X :=
  match p with
  | .none => .none
  | .some p => .some (p u)

def OptionPlot.comp {n} (p : OptionPlot X n) {f : ℝ^m → ℝ^n} (hf : ContDiff ℝ ⊤ f) : OptionPlot X m :=
  match p with
  | .none => .none
  | .some p => .some (p.comp hf)

@[simp]
theorem OptionPlot.eval_none : OptionPlot.eval (X:=X) (n:=n) .none = fun _ => .none := by rfl

@[simp]
theorem OptionPlot.eval_some (f : Plot X n) : OptionPlot.eval (.some f) = fun x => .some (f x) := by rfl

@[simp]
theorem OptionPlot.comp_eval (p : OptionPlot X n) {f : ℝ^m → ℝ^n} (hf : ContDiff ℝ ⊤ f) :
   (p.comp hf).eval = fun u => p.eval (f u) := by
  funext u
  cases p
  · simp; rfl
  · simp[OptionPlot.comp]; apply plotComp_eval


open Diffeology in
instance : Diffeology (Option X) where
  Plot := OptionPlot X
  plotEval := OptionPlot.eval
  plot_ext p q h :=
    match p, q with
    | .none, .none => by rfl
    | .some p, .some q => by
      congr; ext x; simp at h
      have h := congrFun h x
      simp_all
    | .none, .some q => by have h := congrFun h 0; simp[OptionPlot.eval] at h;
    | .some p, .none => by have h := congrFun h 0; simp[OptionPlot.eval] at h;
  plotComp := OptionPlot.comp
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
    DFunLike.coe (F:=Plot (Option X) n) OptionPlot.none = fun _ => .none := by rfl

@[simp]
theorem OptionPlot.eval_some' (f : Plot X n) :
    DFunLike.coe (F:=Plot (Option X) n) (.some f) = fun x => .some (f x) := by rfl

@[simp]
theorem OptionPlot.comp_eval' (p : OptionPlot X n) {f : ℝ^m → ℝ^n} (hf : ContDiff ℝ ⊤ f) :
   DFunLike.coe (F:=Plot (Option X) m) (p.comp hf) = fun u => p.eval (f u) := by apply OptionPlot.comp_eval



open TangentSpace in
instance
    {X : Type*} {TX : outParam (X → Type*)} [Diffeology X]
    [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX] :
    TangentSpace (Option X) (Option.rec PUnit TX) where

  tangentMap {n} p u du :=
    match p with
    | .none => 0
    | .some p => tangentMap p u du

  tangentMap_const := by
    intro n x? u du
    cases x? <;> simp

  exp x dx :=
    match x, dx with
    | .some x, dx => .some (TangentSpace.exp x dx)
    | .none, _ => .none

  exp_at_zero := by intros x dx; cases x; simp; simp

  tangentMap_exp_at_zero x dx t :=
    match x, dx with
    | .none, _ => by simp; rfl
    | .some x, dx => by simp

  tangentMap_linear := by
    intros n p u
    cases p
    case none => simp; fun_prop
    case some p => simp; apply tangentMap_linear
