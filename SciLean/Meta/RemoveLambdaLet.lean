import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic

open Lean 
open Lean.Meta
open Lean.Elab.Tactic

def extractfvar (e : Expr) (v : Expr) : MetaM Expr := do
let V ← inferType v
let fvarid ← v.fvarId!
let E ← inferType e
let u ← getLevel E
match e with
  | Expr.fvar fvarid' _ => if (fvarid'==fvarid) then pure (mkApp (mkConst ``id [u]) E) else (mkAppM `const #[V, e])
  | Expr.app f x _ => 
    match (f.containsFVar fvarid), (x.containsFVar fvarid) with
      | false, false => mkAppM `const #[V, e]
      | false, true => if (x==v) then f else mkAppM `comp #[f, (← extractfvar x v)]
      | true, false => mkAppM `swap #[(← extractfvar f v), x]
      | true, true => mkAppM `subs #[(← extractfvar f v), (← extractfvar x v)]
  | e => e    

partial def removelambdalet (e : Expr) : MetaM Expr :=
match e with
 | Expr.app f x _ => do mkApp (← removelambdalet f) (← removelambdalet x)
 | Expr.lam .. => lambdaTelescope e fun xs b => do 
   let xs := xs.reverse
   let mut b ← removelambdalet b
   for x in xs do
     b ← extractfvar b x
   pure b
 -- | Expr.letE name t v b _ => do
 --     let x ← mkFVar (← mkFreshFVarId)
 --     let b ← b.instantiate #[x]
 --     let b ← extractfvar b x -- This is the problem! x does not really have a type :(
 --     let v ← removelambdalet v
 --     mkApp b v
 | e' => e'

syntax (name := rmlamlet) "rmlamlet" : tactic

def rmlamletCore (mvarId : MVarId) : MetaM (List MVarId) :=
  withMVarContext mvarId do
    let tag      ← getMVarTag mvarId
    let target   ← getMVarType mvarId
    let u        ← getLevel target
    let targetNew ← (removelambdalet target)
    let mvarNew  ← mkFreshExprSyntheticOpaqueMVar targetNew tag
    let eq       ← mkEq target targetNew
    let eqMvar  ← mkFreshExprSyntheticOpaqueMVar eq
    let val  := mkAppN (Lean.mkConst `Eq.mpr [u]) #[target, targetNew, eqMvar, mvarNew]
    -- assignExprMVar mvarId var
    assignExprMVar mvarId mvarNew
    return [mvarNew.mvarId!]

@[tactic rmlamlet] def tacticRemoveLambdaLet : Tactic
| _ => do 
          let mainGoal ← getMainGoal
          let todos ← rmlamletCore mainGoal 
          setGoals todos
          pure ()

