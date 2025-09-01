import Lean.Meta.Tactic.Simp

import Mathlib.Lean.Meta.RefinedDiscrTree
import Mathlib.Lean.Meta.RefinedDiscrTree.Lookup

namespace SciLean

namespace Tactic.RefinedSimp

open Lean Meta Mathlib.Meta.FunProp

initialize registerTraceClass `Meta.Tactic.simp.guard


/-- Optional guard on simp theorems. You can require that an argument is not for example identity
function or constant function after unification. -/
inductive ArgGuard where
  /-- Argument can't be identity function -/
  | notId
  /-- Argument can't be constant function -/
  | notConst
  /-- Argument can't be application of `name` -/
  | notAppOf (name : Name)
  deriving Inhabited, BEq, Repr


/-- Same as SimpTheorem but works with RefinedDiscrTree rather than with normal DescrTree.

It has one additional feature and that is argument guard. For example, you can say that do not apply
this theorem if theorem argument `f` unifies to identity function.
-/
structure RefinedSimpTheorem where
  keys        : List RefinedDiscrTree.DTExpr := []
  /--
    It stores universe parameter names for universe polymorphic proofs.
    Recall that it is non-empty only when we elaborate an expression provided by the user.
    When `proof` is just a constant, we can use the universe parameter names stored in the declaration.
   -/
  levelParams : Array Name := #[]
  proof       : Expr
  priority    : Nat  := eval_prio default
  post        : Bool := true
  /-- `perm` is true if lhs and rhs are identical modulo permutation of variables. -/
  perm        : Bool := false
  /--
    `origin` is mainly relevant for producing trace messages.
    It is also viewed an `id` used to "erase" `simp` theorems from `SimpTheorems`.
  -/
  origin      : Meta.Origin
  /-- `rfl` is true if `proof` is by `Eq.refl` or `rfl`. -/
  rfl         : Bool
  /-- Array of `(theorem argument id, argument guard)` specifying additional constraints on when
  to apply this theorem. For example, if the theorem has arugument `(f : X → X)` with index `3` then
  `guards := #[(3,.notId)]` will stop applying this theorem if `f` unifies to identity function. -/
  guards      : Array (ℕ × ArgGuard) := #[]
  deriving Inhabited, BEq


def RefinedSimpTheorem.getValue (simpThm : RefinedSimpTheorem) : MetaM Expr := do
  if simpThm.proof.isConst && simpThm.levelParams.isEmpty then
    let info ← getConstInfo simpThm.proof.constName!
    if info.levelParams.isEmpty then
      return simpThm.proof
    else
      return simpThm.proof.updateConst! (← info.levelParams.mapM (fun _ => mkFreshLevelMVar))
  else
    let us ← simpThm.levelParams.mapM fun _ => mkFreshLevelMVar
    return simpThm.proof.instantiateLevelParamsArray simpThm.levelParams us


def RefinedSimpTheorem.toSimpTheorem (simpThm : RefinedSimpTheorem) : SimpTheorem := {
  keys        := #[]
  levelParams := simpThm.levelParams
  proof       := simpThm.proof
  priority    := simpThm.priority
  post        := simpThm.post
  perm        := simpThm.perm
  origin      := simpThm.origin
  rfl         := simpThm.rfl
}

abbrev RefinedSimpTheoremTree := RefinedDiscrTree RefinedSimpTheorem


structure RefinedSimpTheorems where
  pre          : RefinedSimpTheoremTree := {}
  post         : RefinedSimpTheoremTree := {}
  deriving Inhabited


/-- -/
initialize refinedSimpTheoremsExt : SimpleScopedEnvExtension RefinedSimpTheorem RefinedSimpTheorems ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun t thm =>
      if thm.post then
        {t with post := thm.keys.foldl (init:=t.post) (fun tree key => tree.insertDTExpr key thm) }
      else
        {t with pre := thm.keys.foldl (init:=t.pre) (fun tree key => tree.insertDTExpr key thm) }
  }


def getTheoremFromConst (declName : Name) (prio : Nat := eval_prio default) (post := true)
    (guards : Array (ℕ × ArgGuard)) : MetaM RefinedSimpTheorem := do
  let info ← getConstInfo declName
  let (_,_,b') ← forallMetaTelescope info.type
  let keys := ← RefinedDiscrTree.mkDTExprs b'.appFn!.appArg! false
  let thm : RefinedSimpTheorem := {
    keys        := keys
    levelParams := info.levelParams.toArray
    proof       := info.value!
    priority    := prio
    post        := post
    perm        := false
    origin      := .decl declName
    rfl         := false
    guards      := guards
  }

  return thm


def addTheorem (declName : Name) (attrKind : AttributeKind := .global)
    (prio : Nat := eval_prio default) (post := true) (guards : Array (ℕ × ArgGuard) := #[]) :
    MetaM Unit := do
  let thm ← getTheoremFromConst declName prio post guards
  refinedSimpTheoremsExt.add thm attrKind


/-- Check if `thm` can be applied to `e` and if the theorem argument `A : W → Set X` is not
a constant function. -/
def theoremGuard (e : Expr) (thm : RefinedSimpTheorem) : MetaM Bool := do
  if thm.guards.size = 0 then return true

  let val  ← thm.getValue
  let type ← inferType val

  let (xs, _, type) ← forallMetaTelescopeReducing type
  let type ← whnf (← instantiateMVars type)
  let lhs := type.appFn!.appArg!

  if (← isDefEq e lhs) then
    for (i,guardType) in thm.guards do
      let x ← instantiateMVars xs[i]!

      match guardType with
      | .notId =>
        let .lam _ _ body _ := x
          | continue
        if body == .bvar 0 then
          trace[Meta.Tactic.simp.guard] "not applying {← ppOrigin thm.origin} to \
                          {← ppExpr e} bacause {← ppExpr x} is identity function"
          return false
      | .notConst =>
        let .lam _ _ body _ := x
          | continue
        if ¬body.hasLooseBVars then
          trace[Meta.Tactic.simp.guard] "not applying {← ppOrigin thm.origin} to \
                          {← ppExpr e} bacause {← ppExpr x} is constant function"
          return false

      | .notAppOf n =>
        if x.isAppOf n then
          trace[Meta.Tactic.simp.guard] "not applying {← ppOrigin thm.origin} to \
                          {← ppExpr e} bacause {← ppExpr x} is application of {n}"
          return false
        continue
    return true
  else
    return false


def refinedRewrite (post : Bool) (e : Expr) : SimpM Simp.Step := do

  let s := (refinedSimpTheoremsExt.getState (← getEnv))
  let s := if post then s.post else s.pre

  let cfg' ← Simp.getConfig
  let candidates ← withConfig (fun cfg => { cfg with iota := cfg'.iota, zeta := cfg'.zeta, zetaDelta := cfg'.zetaDelta }) <|
    s.getMatchWithScoreWithExtra e false

  -- flatten, ignore score but keep extra arguments
  -- then sort by priority
  let candidates := candidates
    |>.foldl (init:=#[]) (fun a c => a ++ c.1.map (fun t => (t,c.2.2)))
    |>.insertionSort (fun (c₁,_) (c₂,_) => c₁.priority > c₂.priority)

  for (thm,numExtraArgs) in candidates do

    unless ← theoremGuard (e.stripArgsN numExtraArgs) thm do continue

    if let some result ← Simp.tryTheoremWithExtraArgs? e thm.toSimpTheorem numExtraArgs then
      trace[Debug.Meta.Tactic.simp] "rewrite result {e} => {result.expr}"
      return .visit result

  return .continue


syntax rsimp_guard := "guard" (ident term),*

open Lean.Parser in
syntax (name := rsimp) "rsimp" (Tactic.simpPre <|> Tactic.simpPost)? (ppSpace prio)? (rsimp_guard)? : attr



private def argumentIndex (declName : Name) (argName : Name) : MetaM (Option Nat) := do

  let info ← getConstInfo declName

  forallTelescope info.type fun xs _ =>
    xs.findIdxM? (fun x => do let name ← x.fvarId!.getUserName; return name == argName)


open Elab Term in
unsafe def elabGuards (declName : Name) (guardStx : Syntax) : TermElabM (Array (ℕ × ArgGuard)) := do
  if guardStx.isNone then return #[]
  match guardStx[0] with
  | `(rsimp_guard| guard $[$ids $gs],*) =>
    let mut grds : (Array (ℕ × ArgGuard)) := #[]
    for id in ids, g in gs do
      let argGuardExpr := Expr.const ``ArgGuard []
      let grd ← evalExpr ArgGuard (Expr.const ``ArgGuard []) (← elabTerm g argGuardExpr)
      let .some argId ← argumentIndex declName id.getId
        | throwError s!"invalid argument {id.getId}"
      grds := grds.push (argId, grd)
    return grds
  | _ =>
    throwUnsupportedSyntax

/-- Initialization of `funProp` attribute -/
unsafe initialize funPropAttr : Unit ←
  registerBuiltinAttribute {
    name  := `rsimp
    descr := "simplification theorem with better support for matching on lambda terms"
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName stx attrKind => do
      let post := if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
      let prio ← getAttrParamOptPrio stx[2]
      let ((grds,_),_) ← (elabGuards declName stx[3]).run {} {} |>.run {}
      let _ ← addTheorem declName attrKind prio post grds |>.run {}
    erase := fun _declName =>
      throwError "can't remove `rsimp` attribute (not implemented yet)"
  }


end Tactic.RefinedSimp

simproc_decl refinedRewritePre (_)  := Tactic.RefinedSimp.refinedRewrite false
simproc_decl refinedRewritePost (_) := Tactic.RefinedSimp.refinedRewrite true
simproc_decl rsimp (_) :=
  Lean.Meta.Simp.andThen
    (Tactic.RefinedSimp.refinedRewrite false)
    (Tactic.RefinedSimp.refinedRewrite true)
