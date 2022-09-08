import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic

import SciLean.Prelude

import Lean.Elab.Tactic.Conv.Basic

namespace Function

  def scomb {α β γ} (f : α → β → γ) (g : α → β) (x : α) := f x (g x)
  def diag {α β} (f : α → α → β) (x : α) := f x x

end Function

namespace Lean.Elab.Tactic.Conv
open Meta


open Lean 
open Lean.Meta
open Lean.Elab.Tactic

def extractfvar (e : Expr) (v : Expr) (lctx : LocalContext) : MetaM Expr := do
withLCtx lctx #[] do
let V ← inferType v
let fvarid := v.fvarId!
let E ← inferType e
let u ← getLevel E
match e with
  | Expr.fvar fvarid' => if (fvarid'==fvarid) then pure (mkApp (mkConst ``id [u]) E) else (mkAppM ``Function.const #[V, e])
  | Expr.app f x => 
    match (f.containsFVar fvarid), (x.containsFVar fvarid) with
      | false, false => mkAppM ``Function.const #[V, e]
      | false, true => if (x==v) then pure f else mkAppM ``Function.comp #[f, (← extractfvar x v lctx)]
      | true, false => mkAppM ``Function.swap #[(← extractfvar f v lctx), x]
      | true, true => -- mkAppM `subs #[(← extractfvar f v lctx), (← extractfvar x v lctx)]
                      if (x==v) then 
                        mkAppM ``Function.diag #[(← extractfvar f v lctx)]
                      else
                        mkAppM ``Function.scomb #[(← extractfvar f v lctx), (← extractfvar x v lctx)]
  | e => pure e    

partial def removelambdalet (e : Expr) (lctx : LocalContext) : MetaM Expr :=
withLCtx lctx #[] do
match e with
 | Expr.app f x => pure $ mkApp (← removelambdalet f lctx) (← removelambdalet x lctx)
 | Expr.lam .. => lambdaTelescope e fun xs b => do
   let xs := xs.reverse
   let mut b ← removelambdalet b (← getLCtx)
   -- let B ← inferType b
   for x in xs do
     -- if ¬(B.containsFVar x.fvarId!) then
     b ← extractfvar b x (← getLCtx)
     -- else
     --   b ← mkLambdaFVars #[x] b
   pure b
 | Expr.letE n t v b _ => do
     let lctx ← getLCtx
     let fvarId ← mkFreshFVarId
     let lctx := lctx.mkLetDecl fvarId n t v
     let fvar := mkFVar fvarId
     let b := b.instantiate #[fvar]
     let b ← removelambdalet b lctx
     let b ← extractfvar b fvar lctx
     let v ← removelambdalet v lctx
     pure $ mkApp b v
 | e' => pure e'

syntax (name := rmlamlet) "rmlamlet" : tactic

def rmlamletCore (mvarId : MVarId) : MetaM (List MVarId) :=
  mvarId.withContext do
    let tag      ← mvarId.getTag
    let target   ← mvarId.getType
    -- let u        ← getLevel target
    let targetNew ← (removelambdalet target (← getLCtx))
    let mvarNew  ← mkFreshExprSyntheticOpaqueMVar targetNew tag
    -- let eq       ← mkEq target targetNew
    -- let eqMvar  ← mkFreshExprSyntheticOpaqueMVar eq
    -- let val  := mkAppN (Lean.mkConst `Eq.mpr [u]) #[target, targetNew, eqMvar, mvarNew]
    -- assignExprMVar mvarId var
    mvarId.assign mvarNew
    return [mvarNew.mvarId!]

@[tactic rmlamlet] def tacticRemoveLambdaLet : Tactic
| _ => do 
          let mainGoal ← getMainGoal
          let todos ← rmlamletCore mainGoal 
          setGoals todos
          pure ()

syntax (name := conv_rmlamlet) "rmlamlet" : conv

@[tactic conv_rmlamlet] def tacticConvRemoveLambdaLet : Tactic := 
fun stx => withMainContext do
          let lhs ← instantiateMVars (← getLhs)
          changeLhs (← removelambdalet lhs (← getLCtx))
          pure ()


example : (λ x : Nat => x + x) = (λ _ => 0) := 
by 
  rmlamlet
  admit
  done

-- syntax (name := print_goal) "print_goal" : conv

-- @[tactic print_goal] def tacticPrintGoal : Tactic := 
-- fun stx => withMainContext do
--           let mainGoal ← getMainGoal
--           withMVarContext mainGoal do
--             let (lhs, rhs) ← getLhsRhsCore mainGoal
--             let lhs ← instantiateMVars lhs
--             let rhs ← instantiateMVars rhs
--             IO.println s!"Goal: {← getMVarType (← getMainGoal)}"
--             IO.println s!"lhs & rhs: {lhs} | {rhs}"
--             pure ()


-- syntax (name := print_lhs) "print_lhs" : conv

-- @[tactic print_lhs] def tacticPrintLhs : Tactic := 
-- fun stx => withMainContext do
--           changeLhs (← instantiateMVars (← getLhs))
--           IO.println s!"Lhs: {← instantiateMVars (← getLhs)}"
--           pure ()


-- syntax (name := print_rhs) "print_rhs" : conv

-- @[tactic print_rhs] def tacticPrintRhs : Tactic := 
-- fun stx => withMainContext do 
--           IO.println s!"Rhs: {← instantiateMVars (← getRhs)}"
--           pure ()



-- def test : id (id (λ x : Nat => id (id x))) = λ x => x := by

--   conv =>
--     print_lhs
--     lhs
--     print_lhs
--     enter [1,1]
--     print_lhsv
--     rmlamlet
--     enter [x]
--     simp
--     print_lhs
--     print_rhs
--     print_goal
--   done

  
  
    



