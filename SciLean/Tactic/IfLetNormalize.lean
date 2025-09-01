import Mathlib.Tactic.SplitIfs

namespace SciLean

private theorem let_ite_eq_ite_let {α β} {c : Prop} [Decidable c] (t e : α) (f : α → β) :
    (let x := if c then t else e
    f x)
    =
    (if c then
      let x := t
      f x
    else
      let x := e
      f x) := by
  split_ifs <;> rfl

private theorem let_dite_eq_dite_let {α β} {c : Prop} [Decidable c]
    (t : c → α) (e : ¬c → α) (f : α → β) :
    (let x := dite c t e
    f x)
    =
    (if h : c then
      let x := t h
      f x
    else
      let x := e h
      f x) := by
  split_ifs <;> rfl


open Lean Meta in
simproc_decl let_ite_normalize (_) := fun e => do
  match e with
  | .letE n t v b _ =>
    if v.isAppOfArity ``ite 5 then
      let f := Expr.lam n t b default
      let ve := v.appArg!
      let vt := v.appFn!.appArg!
      let decInst := v.appFn!.appFn!.appArg!
      let prf ← mkAppOptM ``let_ite_eq_ite_let #[none,none,none,decInst, vt, ve, f]
      let rhs := (← inferType prf).appArg!
      return .visit { expr := rhs, proof? := prf}
    if v.isAppOfArity ``dite 5 then
      let f := Expr.lam n t b default
      let ve := v.appArg!
      let vt := v.appFn!.appArg!
      let decInst := v.appFn!.appFn!.appArg!
      let prf ← mkAppOptM ``let_dite_eq_dite_let #[none,none,none,decInst, vt, ve, f]
      let rhs := (← inferType prf).appArg!
      return .visit { expr := rhs, proof? := prf}
    return .continue
  | _ => return .continue
