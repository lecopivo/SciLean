import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.TangentSpace
import SciLean.Tactic.InferVar

namespace SciLean

local notation:max "ℝ^" n:max => Fin n → ℝ

variable
  {X : Type*} {TX : outParam (X → Type*)} [Diffeology X] [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
  {Y : Type*} {TY : outParam (Y → Type*)} [Diffeology Y] [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY]
  {Z : Type*} {TZ : outParam (Z → Type*)} [Diffeology Z] [∀ z, AddCommGroup (TZ z)] [∀ z, Module ℝ (TZ z)] [TangentSpace Z TZ]


def NonePlot {n} (p : ℝ^n → Option X) : Prop := ∀ x, p x = none
def SomePlot {n} (p : ℝ^n → Option X) : Prop :=
  ∃ q : ℝ^n → X,
    (∀ x, p x = some (q x))
    ∧
    q ∈ Diffeology.plots n

def NonePlot.notSomePlot {n} {p : ℝ^n → Option X} (hp : NonePlot p) :
  ¬SomePlot p := sorry

noncomputable
def SomePlot.val {n} {p : ℝ^n → Option X} (hp : SomePlot p) (u : ℝ^n) : X :=
  Classical.choose hp u

@[simp]
theorem SomePlot.val_const {x : X} (hp : SomePlot fun _ : ℝ^n => some x) :
    hp.val = fun _ => x := sorry

@[simp]
theorem SomePlot.val_some {p : ℝ^n → X} (hp : SomePlot (fun x => some (p x))) :
    hp.val = p := sorry

noncomputable
def SomePlot.valAt {n} {p : ℝ^n → Option X} (hp : SomePlot p) (u : ℝ^n) :
    p u = some (hp.val u) :=
  sorry

noncomputable
def NonePlot.valAt {n} {p : ℝ^n → Option X} (hp : NonePlot p) (u : ℝ^n) :
    p u = none :=
  sorry


open Diffeology in
@[simp]
theorem SomePlot.of_some (p : ℝ^n → X) (hp : p ∈ plots n) : SomePlot (fun x => some (p x)) := sorry


open Diffeology in
instance : Diffeology (Option X) where
  plots := fun n p => NonePlot p ∨ SomePlot p
  plot_comp := by
    intros n m p f hp hf
    cases hp
    case inl h => left; intro x; exact h (f x)
    case inr h =>
      right
      cases' h with q hq
      apply Exists.intro (q ∘ f)
      constructor
      · intro x; simp[Function.comp_def,hq.1 (f x)]
      · apply Diffeology.plot_comp hq.2 hf
  const_plot := by
    intros n x
    cases x
    case none => left; simp
    case some x =>
      right
      apply Exists.intro (fun _ => x)
      constructor; simp only [implies_true]; apply Diffeology.const_plot




--------------------------------------------------------------------------------
-- Algebra instances for Sum.rec ------------------------------------------
--------------------------------------------------------------------------------
-- There are some issues with defEq

@[reducible]
instance {α} {β : α → Type*} [∀ a, Zero (β a)] (a? : Option α) : Zero (Option.rec PUnit β a?) :=
  match a? with
  | .none => by infer_instance
  | .some _ => by infer_instance

@[reducible]
instance {α} {β : α → Type*} [∀ a, One (β a)] (a? : Option α) : One (Option.rec PUnit β a?) :=
  match a? with
  | .none => by infer_instance
  | .some _ => by infer_instance

@[reducible]
instance {α} {β : α → Type*} [∀ a, Add (β a)] (a? : Option α) : Add (Option.rec PUnit β a?) :=
  match a? with
  | .none => by infer_instance
  | .some _ => by infer_instance

@[reducible]
instance {α} {β : α → Type*} {S : Type*} [∀ a, SMul S (β a)] (a? : Option α) : SMul S (Option.rec PUnit β a?) :=
  match a? with
  | .none => by infer_instance
  | .some _ => by infer_instance

@[reducible]
instance {α} {β : α → Type*} [∀ a, Neg (β a)] (a? : Option α) : Neg (Option.rec PUnit β a?) :=
  match a? with
  | .none => by infer_instance
  | .some _ => by infer_instance

@[reducible]
instance {α} {β : α → Type*} [∀ a, Sub (β a)] (a? : Option α) : Sub (Option.rec PUnit β a?) :=
  match a? with
  | .none => by infer_instance
  | .some _ => by infer_instance

@[reducible]
instance {α} {β : α → Type*} [∀ a, Norm (β a)] (a? : Option α) : Norm (Option.rec PUnit β a?) :=
  match a? with
  | .none => by infer_instance
  | .some _ => by infer_instance

@[reducible]
instance {α} {β : α → Type*} [∀ a, Dist (β a)] (a? : Option α) : Dist (Option.rec PUnit β a?) :=
  match a? with
  | .none => by infer_instance
  | .some _ => by infer_instance

@[reducible]
instance {α} {β : α → Type*} [∀ a, EDist (β a)] (a? : Option α) : EDist (Option.rec PUnit β a?) :=
  match a? with
  | .none => by infer_instance
  | .some _ => by infer_instance

@[reducible]
instance {α} {β : α → Type*} [∀ a, TopologicalSpace (β a)] (a? : Option α) : TopologicalSpace (Option.rec PUnit β a?) :=
  match a? with
  | .none => by infer_instance
  | .some _ => by infer_instance

@[reducible]
instance {α} {β : α → Type*} [∀ a, UniformSpace (β a)] (a? : Option α) : UniformSpace (Option.rec PUnit β a?) :=
  match a? with
  | .none => by infer_instance
  | .some _ => by infer_instance

@[reducible]
instance {α} {β : α → Type*} [∀ a, MetricSpace (β a)] (a? : Option α) : MetricSpace (Option.rec PUnit β a?) :=
  match a? with
  | .none => by infer_instance
  | .some _ => by infer_instance

@[reducible]
instance {α} {β : α → Type*} [∀ a, AddCommGroup (β a)] (a? : Option α) : AddCommGroup (Option.rec PUnit β a?) :=
  match a? with
  | .none => by infer_instance
  | .some _ => by infer_instance

@[reducible]
instance {α} {β : α → Type*} [∀ a, NormedAddCommGroup (β a)] (a? : Option α) : NormedAddCommGroup (Option.rec PUnit β a?) :=
  match a? with
  | .none => by infer_instance
  | .some _ => by infer_instance

@[reducible]
instance {α} {β : α → Type*} {K} [Semiring K] [∀ a, AddCommGroup (β a)] [∀ a, Module K (β a)] (a? : Option α) : Module K (Option.rec PUnit β a?) :=
  match a? with
  | .none => by infer_instance
  | .some _ => by infer_instance


theorem cast_to_rhs (x : α) (y : β) (h : α = β) :
  (cast h x = y) = (x = cast (by rw[h]) y) := by subst h; simp

open TangentSpace in
theorem tangentMap_congr {p q : ℝ^n → X} (h : q = p := by simp; infer_var) :
  tangentMap p u du = cast (by simp[h]) (tangentMap q u du) := by subst h; simp

set_option pp.proofs.withType true in
open TangentSpace Classical in
instance
    {X : Type*} {TX : outParam (X → Type*)} [Diffeology X]
    [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX] :
    TangentSpace (Option X) (Option.rec PUnit TX) where

  tangentMap {n} p u du :=
    if q : SomePlot p then
      cast (by rw[q.valAt u]) (tangentMap q.val u du)
    else
      0
  tangentMap_const := by
    intro n x t dt
    cases x
    case none => simp
    case some x =>
      simp
      intro q
      rw[tangentMap_congr (by simp; infer_var)]
      fun_trans

  exp x dx t :=
    match x, dx with
    | .some x, dx => .some (TangentSpace.exp x dx t)
    | .none, _ => none
  exp_at_zero := by intros x dx; cases x <;> simp
  exp_is_plot x dx:= by
    cases x
    case none => left; simp[NonePlot]
    case some x =>
      right
      apply Exists.intro (TangentSpace.exp x dx)
      simp[TangentSpace.exp_is_plot]

  tangentMap_exp_at_zero := by
    intros x dx t
    cases x
    · simp
    · simp[TangentSpace.exp_is_plot]
      rw[tangentMap_congr (by simp[TangentSpace.exp_is_plot]; infer_var)]
      simp

  tangentMap_linear := by
    intros n c hc x
    cases hc
    case inl hc =>
      simp_all[hc.notSomePlot]
      constructor
      · intro x y; simp; sorry
      · intro r y;
        have h : (0 : Option.rec PUnit TX (c x)) = r • 0 := by sorry
        convert h
        have hh := hc.valAt x
        simp[instSMulRecType_sciLean_1]
        subst hh


    case inr hc =>
      simp_all
      constructor
      · intro x y; simp[add_push]; sorry
      · sorry
