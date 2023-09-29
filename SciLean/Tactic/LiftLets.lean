/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Tomas Skrivan
-/
import Lean
import Qq
import SciLean.Lean.Meta.Basic

/-!
# The `lift_lets` tactic

This module defines a tactic `lift_lets` that can be used to pull `let` bindings as far out
of an expression as possible.
-/

open Lean Elab Parser Meta Tactic

/-- Configuration for `Lean.Expr.liftLets` and the `lift_lets` tactic. -/
structure Lean.Expr.LiftLetsConfig where
  /-- Whether to lift lets out of proofs. The default is not to. -/
  proofs : Bool := false
  /-- Whether to merge let bindings if they have the same type and value.
  This test is by syntactic equality, not definitional equality.
  The default is to merge. -/
  merge : Bool := true

/-- Is `e` function type with no dependent types?
-/
def isSimpleFunType (e : Expr) : Bool :=
  if ¬e.consumeMData.isForall then false else go e
where 
  go (e : Expr) : Bool :=
    match e with
    | .forallE _ t b _ => 
      if t.hasLooseBVars || b.hasLooseBVars then
        false
      else
        go b
    | .mdata _ e => go e
    | _ => true


private def buildMk (mk : Expr) (mks : List Expr) (vars vals : Array Expr) : MetaM Expr :=
  match mks with 
  | [] => mkLambdaFVars vars (mkAppN mk vals)
  | mk' :: mks' => 
    lambdaTelescope mk' fun xs b => 
      buildMk mk mks' (vars++xs) (vals.push b)              

/-- Decomposes an element `e` that is a nested application of constructors

For example, calling this function on `x : (Nat×Nat)×Nat` returns `(#[x.1.1, x.1.2, x.1], fun a b c => ((a,b),c))`
-/
private partial def splitByCtorsImpl (e : Expr) : MetaM (Array Expr × Expr) := do

  let E ← inferType e
  let idE := Expr.lam `x E (.bvar 0) default

  let .const structName _ := E.getAppFn'
    | return (#[e], idE)

  -- not structure
  let .some _ := getStructureInfo? (← getEnv) structName
    | return (#[e], idE)

  let ctorVal := getStructureCtor (← getEnv) structName

  let fn := e.getAppFn
  let args := e.getAppArgs'

  -- not application of ctor
  if fn.constName? ≠ .some ctorVal.name then 
    return (#[e], idE)
    
  -- not fully applied ctor
  if args.size ≠ ctorVal.numParams + ctorVal.numFields then
    return (#[e], idE)

  let mk := mkAppN fn args[0:ctorVal.numParams]

  -- if ¬(isSimpleFunType (← inferType mk)) then
  --   return (#[e], idE)

  let fields : Array _ := args[ctorVal.numParams : ctorVal.numParams + ctorVal.numFields]
  let (eis, mks) := (← fields.mapM splitByCtorsImpl).unzip

  let mk ← buildMk mk mks.toList #[] #[]

  return (eis.flatten, mk)


/-- Decomposes an element `e` that is a nested application of constructors

For example, calling this function on `x : (Nat×Nat)×Nat` returns `(#[x.1.1, x.1.2, x.1], fun a b c => ((a,b),c))`
-/
def splitByCtors (e : Expr) : MetaM (Option (Array Expr × Expr)) := do
  let r ← splitByCtorsImpl e
  if r.1.size = 1 then
    return none
  else
    return r


inductive ReplacePost where
  | yield (e : Expr)
  | done (e : Expr)


def ReplacePost.val (r : ReplacePost) : Expr :=
  match r with
  | yield e  => e
  | done e => e


private partial def replaceFVarAndPostImpl (e : Expr) (id : FVarId) (val : Expr) (post : Expr → MetaM ReplacePost) : MetaM ReplacePost :=
  if ¬e.hasFVar then
    return .done e
  else
  match e with
  | .fvar id' => 
    if id' == id then
      return .yield val
    else
      return .done e
  | .app f x => do
    match ← replaceFVarAndPostImpl f id val post, ← replaceFVarAndPostImpl x id val post with
    | .yield f', .yield x'
    | .yield f', .done x'
    | .done f', .yield x' => post (.app f' x')
    | .done f', .done x' => return .done (.app f' x')
  | .lam n t b bi => do
    let t' ← replaceFVarAndPostImpl t id val post
    withLocalDecl n bi t'.val fun var => do
      match t', ← replaceFVarAndPostImpl (b.instantiate1 var) id val post with
      | .yield _, .yield b' 
      | .yield _, .done b' 
      | .done _, .yield b' => post (← mkLambdaFVars #[var] b')
      | .done _, .done b' => return .done (← mkLambdaFVars #[var] b')
  | .forallE n t b bi => do
    let t' ← replaceFVarAndPostImpl t id val post
    withLocalDecl n bi t'.val fun var => do
      match t', ← replaceFVarAndPostImpl (b.instantiate1 var) id val post with
      | .yield _, .yield b' 
      | .yield _, .done b' 
      | .done _, .yield b' => post (← mkForallFVars #[var] b')
      | .done _, .done b' => return .done (← mkForallFVars #[var] b')
  | .letE n t v b _ => do
    let t' ← replaceFVarAndPostImpl t id val post
    withLocalDecl n .default t'.val fun var => do
      match ← replaceFVarAndPostImpl v id val post, ← replaceFVarAndPostImpl (b.instantiate1 var) id val post with
      | .yield v', .yield b'
      | .yield v', .done b'
      | .done v', .yield b' =>
        post (.letE n (← inferType v') v' (b'.abstract #[var]) false)
      | .done v', .done b' =>
        return .done (.letE n (← inferType v') v' (b'.abstract #[var]) false)
  | .mdata _ e => replaceFVarAndPostImpl e id val post
  | .proj n i e => do
    match ← replaceFVarAndPostImpl e id val post with
    | .yield e' => post (.proj n i e')
    | .done e' => return .done (.proj n i e')
  | .mvar _ => do replaceFVarAndPostImpl (← instantiateMVars e) id val post
  | e => return .done e


def replaceFVarAndPost (e : Expr) (id : FVarId) (val : Expr) (post : Expr → MetaM ReplacePost) : MetaM Expr := do pure (← replaceFVarAndPostImpl e id val post).val


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
        match ← splitByCtors v' with
        | .some (vs', mk') => 
          let ns := (Array.range vs'.size).map fun i => n.appendAfter (toString i)
          withLetDecls ns vs' fun fvars' =>
          withLocalDecl n .default t' fun fvar => do
            let fvar' := (mkAppN mk' fvars').headBeta
            let b' ← replaceFVarAndPost (b.instantiate1 fvar) fvar.fvarId! fvar'
              (post := fun e => do
                match ← reduceProjOfCtor? e with
                | .some e' => return .yield e'
                | .none => return .done e)
            b'.liftLetsAux config (fvars ++ fvars') f
        | .none => 
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

/-- Take all the `let`s in an expression and move them outwards as far as possible.
All top-level `let`s are added to the local context, and then `f` is called with the list
of local bindings (each an fvar) and the new expression.

Let bindings are merged if they have the same type and value.

Use `e.liftLets mkLetFVars` to get a defeq expression with all `let`s lifted as far as possible. -/
def Lean.Expr.liftLets (e : Expr) (f : Array Expr → Expr → MetaM Expr)
    (config : LiftLetsConfig := {}) : MetaM Expr :=
  e.liftLetsAux config #[] f


open Qq
#eval show MetaM Unit from do
  
  let e := q(
    fun x => 
    let a := 
      let b := (10,(20,30))
      let i : Fin 10 := ⟨5, by simp⟩
      let c := b.1 + 3
      b.2.2 + c + 4 + i.1
    let d := 
      let e := 11
      a + 4 + e + x
    a + d
    )

  let e' ← e.liftLets mkLetFVars

  IO.println (← ppExpr e')
  

#eval show MetaM Unit from do

  withLocalDeclQ `x .default q(Nat × Nat × Nat) fun x => do
  let e := q(
  let a1 := 42
  let a2 := a1
  let a3 := a2
  let a4 := a3
  let a5 := a4
  let a6 := a5
  let a7 := a6
  let a8 := a7
  let a9 := a8
  let a10 := a9
  let a11 := a10
  let a12 := a11
  let a13 := a12
  let a14 := a13
  let a15 := a14
  let a16 := a15
  let a17 := a16
  let a18 := a17
  let a19 := a18
  let a20 := a19
  let a21 := a20
  let a22 := a21
  let a23 := a22
  let a24 := a23
  let a25 := a24
  let a26 := a25
  let a27 := a26
  let a28 := a27
  let a29 := a28
  let a30 := a29
  let a31 := a30
  let a32 := a31
  let a33 := a32
  let a34 := a33
  let a35 := a34
  let a36 := a35
  let a37 := a36
  let a38 := a37
  let a39 := a38
  let a40 := a39
  let a41 := a40
  let a42 := a41
  let a43 := a42
  let a44 := a43
  let a45 := a44
  let a46 := a45
  let a47 := a46
  let a48 := a47
  let a49 := a48
  let a50 := a49
  let a51 := a50
  let a52 := a51
  let a53 := a52
  let a54 := a53
  let a55 := a54
  let a56 := a55
  let a57 := a56
  let a58 := a57
  let a59 := a58
  let a60 := a59
  let a61 := a60
  let a62 := a61
  let a63 := a62
  let a64 := a63
  let a65 := a64
  let a66 := a65
  let a67 := a66
  let a68 := a67
  let a69 := a68
  let a70 := a69
  let a71 := a70
  let a72 := a71
  let a73 := a72
  let a74 := a73
  let a75 := a74
  let a76 := a75
  let a77 := a76
  let a78 := a77
  let a79 := a78
  let a80 := a79
  let a81 := a80
  let a82 := a81
  let a83 := a82
  let a84 := a83 + $x.1
  let a85 := a84
  let a86 := a85
  let a87 := a86
  let a88 := a87
  let a89 := a88
  let a90 := a89
  let a91 := a90 + $x.2.1
  let a92 := a91
  let a93 := a92
  let a94 := a93
  let a95 := a94
  let a96 := a95
  let a97 := a96 + $x.2.2
  let a98 := a97
  let a99 := a98
  let a100 := a99
  a100)


  let e' ← replaceFVarAndPost e x.fvarId! q((1,2,3)) 
    (fun e => do
      IO.println s!"running post on {← ppExpr e}"
      match ← reduceProjOfCtor? e with
      | .some e' => return .yield e'
      | .none => return .done e)
  IO.println (← ppExpr e')
