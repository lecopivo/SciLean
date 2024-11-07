import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.PUnitInstances.Module
import Mathlib.Analysis.Normed.Module.Basic

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
