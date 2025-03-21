/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Tomas Skrivan
-/
import Lean
import Qq

import SciLean.Lean.Meta.Basic
import SciLean.Lean.Meta.Structure
import SciLean.Lean.Meta.Replace


open Lean Elab Parser Meta Tactic SciLean

/-- Configuration for `Lean.Expr.liftLets` and the `lift_lets` tactic. -/
structure Lean.Expr.LiftLetsConfig where
  /-- Whether to lift lets out of proofs. The default is not to. -/
  proofs : Bool := false
  /-- Whether to merge let bindings if they have the same type and value.
  This test is by syntactic equality, not definitional equality.
  The default is to merge. -/
  merge : Bool := true
  /-- Whether to split lets with structure constructors. Let bindings like
  `let a := (x,y)` will be split into two let bindings `let a0 := x; let a1 := y` -/
  splitCtors : Bool := true
  /-- Whether remove let bindings if the the value is just a fvar. -/
  removeFVar : Bool := true
  /-- Whether remove let bindings if the the value is a numerical constant i.e. OfNat or OfScientific -/
  removeNum : Bool := true
  /-- Whether remove let bindings if the the value is a lambda function -/
  removeLambda : Bool := true


/--
Auxiliary definition for `Lean.Expr.liftLets`. Takes a list of the accumulated fvars.
This list is used during the computation to merge let bindings.
-/
private partial def Lean.Expr.liftLetsAux (config : LiftLetsConfig) (e : Expr) (fvars : Array Expr)
    (f : Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  if (e.find? Expr.isLet).isNone then
    -- If `e` contains no `let` expressions, then we can avoid recursing into it.
    return ← f fvars e
  if !config.proofs then
    if ← Meta.isProof e then
      return ← f fvars e
  match e with
  | .letE n t v b _ =>
    t.liftLetsAux config fvars fun fvars t' =>
      v.liftLetsAux config fvars fun fvars v' => do
        if config.merge then
          -- Eliminate the let binding if there is already one of the same type and value.
          let fvar? ← fvars.findM? (fun fvar => do
            let decl ← fvar.fvarId!.getDecl
            return decl.type == t' && decl.value? == some v')
          if let some fvar' := fvar? then
            return ← (b.instantiate1 fvar').liftLetsAux config fvars f

        if config.splitCtors then
          if let .some (vs', _, mk') ← splitByCtors? v' then
            let names := (Array.range vs'.size).map fun i => n.appendAfter (toString i)
            return ← withLetDecls names vs' fun fvars' => do
              let fvar' := (mkAppN mk' fvars').headBeta
              let mut b' ← instantiate1AndProject b t' fvar'
              let mut fvars'' := #[]
              for v' in vs', fvar' in fvars' do
                if removeLet v' then
                  b' := b'.replaceFVar fvar' v'
                else
                  fvars'' := fvars''.push fvar'
              b'.liftLetsAux config (fvars ++ fvars'') f

        if removeLet v' then
          return ← (b.instantiate1 v').liftLetsAux config fvars f

        withLetDecl n t' v' fun fvar =>
          (b.instantiate1 fvar).liftLetsAux config (fvars.push fvar) f
  | .app x y =>
    x.liftLetsAux config fvars fun fvars x' => y.liftLetsAux config fvars fun fvars y' =>
      f fvars (.app x' y')
  | .proj n idx s =>
    s.liftLetsAux config fvars fun fvars s' => f fvars (.proj n idx s')
  | .lam n t b i =>
    t.liftLetsAux config fvars fun fvars t => do
      -- Enter the binding, do liftLets, and lift out liftable lets
      let e' ← withLocalDecl n i t fun fvar => do
        (b.instantiate1 fvar).liftLetsAux config fvars fun fvars2 b => do
          -- See which bindings can't be migrated out
          let deps ← collectForwardDeps #[fvar] false
          let fvars2 := fvars2[fvars.size:].toArray
          let (fvars2, fvars2') := fvars2.partition deps.contains
          mkLetFVars fvars2' (← mkLambdaFVars #[fvar] (← mkLetFVars fvars2 b))
      -- Re-enter the new lets; we do it this way to keep the local context clean
      insideLets e' fvars fun fvars e'' => f fvars e''
  | .forallE n t b i =>
    t.liftLetsAux config fvars fun fvars t => do
      -- Enter the binding, do liftLets, and lift out liftable lets
      let e' ← withLocalDecl n i t fun fvar => do
        (b.instantiate1 fvar).liftLetsAux config fvars fun fvars2 b => do
          -- See which bindings can't be migrated out
          let deps ← collectForwardDeps #[fvar] false
          let fvars2 := fvars2[fvars.size:].toArray
          let (fvars2, fvars2') := fvars2.partition deps.contains
          mkLetFVars fvars2' (← mkForallFVars #[fvar] (← mkLetFVars fvars2 b))
      -- Re-enter the new lets; we do it this way to keep the local context clean
      insideLets e' fvars fun fvars e'' => f fvars e''
  | .mdata _ e => e.liftLetsAux config fvars f
  | _ => f fvars e
where
  -- Like the whole `Lean.Expr.liftLets`, but only handles lets
  insideLets {α} (e : Expr) (fvars : Array Expr) (f : Array Expr → Expr → MetaM α) : MetaM α := do
    match e with
    | .letE n t v b _ =>
      withLetDecl n t v fun fvar => insideLets (b.instantiate1 fvar) (fvars.push fvar) f
    | _ => f fvars e
  /-- Replaces `.bvar 0` of type `t` in `e` with `val` and potentially reduce projections -/
  instantiate1AndProject (e : Expr) (t : Expr) (val : Expr) : MetaM Expr := do
    withLocalDeclD .anonymous t fun fvar => do
      replaceFVarAndPost (e.instantiate1 fvar) fvar.fvarId! val
        (post := fun e => do
          match ← reduceProjOfCtor? e with
          | .some e' => return .yield e'
          | .none => return .done e)
  removeLet (v : Expr) : Bool :=
    if config.removeFVar && v.isFVar then
      true
    else if config.removeNum &&
      (v.isAppOfArity' ``OfNat.ofNat 3 ||
       v.isAppOfArity' ``OfScientific.ofScientific 5) then
      true
    else if config.removeLambda && v.isLambda then
      true
    else
      false

/-- Take all the `let`s in an expression and move them outwards as far as possible.
All top-level `let`s are added to the local context, and then `f` is called with the list
of local bindings (each an fvar) and the new expression.

Let bindings are merged if they have the same type and value.

Use `e.liftLets mkLetFVars` to get a defeq expression with all `let`s lifted as far as possible. -/
def Lean.Expr.liftLets (e : Expr) (f : Array Expr → Expr → MetaM Expr)
    (config : LiftLetsConfig := {}) : MetaM Expr :=
  e.liftLetsAux config #[] f


def Lean.Expr.letNormalize (e : Expr)
    (config : LiftLetsConfig := {}) : MetaM Expr :=
  e.liftLetsAux config #[] mkLetFVars




-- open Qq
-- #eval show MetaM Unit from do

--   let e := q(
--     fun x y =>
--       let a := x
--       let b := a + y
--       let c := 42
--       x + y + a + b + c)

--   lambdaLetTelescope e fun xs b => do
--     let xs' ← mergeFVars xs[0:2] xs[2:]

--     IO.println (← xs'.mapM ppExpr)


-- open Qq
-- #eval show MetaM Unit from do

--   let e := q(
--     fun x =>
--     let a :=
--       let b := (10,(20,30))
--       let i : Fin 10 := ⟨5, by simp⟩
--       let c := b.1 + 3
--       b.2.2 + c + 4 + i.1
--     let d :=
--       let e := 11
--       a + 4 + e + x
--     let z := a + d
--     let w := z
--     w
--     )

--   let e' ← e.letNormalize (config := {removeNum := true})

--   IO.println (← ppExpr e')


-- #eval show MetaM Unit from do

--   withLocalDeclQ `x .default q(Nat × Nat × Nat) fun x => do
--   let e := q(
--   let a1 := 42
--   let a2 := a1
--   let a3 := a2
--   let a4 := a3
--   let a5 := a4
--   let a6 := a5
--   let a7 := a6
--   let a8 := a7
--   let a9 := a8
--   let a10 := a9
--   let a11 := a10
--   let a12 := a11
--   let a13 := a12
--   let a14 := a13
--   let a15 := a14
--   let a16 := a15
--   let a17 := a16
--   let a18 := a17
--   let a19 := a18
--   let a20 := a19
--   let a21 := a20
--   let a22 := a21
--   let a23 := a22
--   let a24 := a23
--   let a25 := a24
--   let a26 := a25
--   let a27 := a26
--   let a28 := a27
--   let a29 := a28
--   let a30 := a29
--   let a31 := a30
--   let a32 := a31
--   let a33 := a32
--   let a34 := a33
--   let a35 := a34
--   let a36 := a35
--   let a37 := a36
--   let a38 := a37
--   let a39 := a38
--   let a40 := a39
--   let a41 := a40
--   let a42 := a41
--   let a43 := a42
--   let a44 := a43
--   let a45 := a44
--   let a46 := a45
--   let a47 := a46
--   let a48 := a47
--   let a49 := a48
--   let a50 := a49
--   let a51 := a50
--   let a52 := a51
--   let a53 := a52
--   let a54 := a53
--   let a55 := a54
--   let a56 := a55
--   let a57 := a56
--   let a58 := a57
--   let a59 := a58
--   let a60 := a59
--   let a61 := a60
--   let a62 := a61
--   let a63 := a62
--   let a64 := a63
--   let a65 := a64
--   let a66 := a65
--   let a67 := a66
--   let a68 := a67
--   let a69 := a68
--   let a70 := a69
--   let a71 := a70
--   let a72 := a71
--   let a73 := a72
--   let a74 := a73
--   let a75 := a74
--   let a76 := a75
--   let a77 := a76
--   let a78 := a77 + $x.1
--   let a79 := a78
--   let a80 := a79
--   let a81 := a80
--   let a82 := a81
--   let a83 := a82
--   let a84 := a83
--   let a85 := a84 + $x.2.1
--   let a86 := a85
--   let a87 := a86
--   let a88 := a87
--   let a89 := a88
--   let a90 := a89
--   let a91 := a90
--   let a92 := a91 + $x.2.2
--   let a93 := a92
--   let a94 := a93
--   let a95 := a94
--   let a96 := a95
--   let a97 := a96
--   let a98 := a97
--   let a99 := a98
--   let a100 := a99
--   a100)

--   let e' ← replaceFVarAndPost e x.fvarId! q((1,2,3))
--     (fun e => do
--       IO.println s!"running post on {← ppExpr e}"
--       match ← reduceProjOfCtor? e with
--       | .some e' => return .yield e'
--       | .none => return .done e)

--   IO.println (← ppExpr e')
