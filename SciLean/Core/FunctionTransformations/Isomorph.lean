import SciLean.Core.Objects.IsomorphicType

import SciLean.Tactic.FTrans.Basic

open Lean

namespace SciLean

variable 
  {α β γ : Type _}
  {α' β' γ' : outParam (Type _)}
  (tag : Name)
  [IsomorphicType tag α α']
  [IsomorphicType tag β β']
  [IsomorphicType tag γ γ']

namespace isomorph

variable (α)
theorem id_rule 
  : isomorph tag (fun (x : α) => x)
    =
    fun (x : α') => x :=
by
  funext _; simp[isomorph]


theorem const_rule (y : β)
  : isomorph tag (fun (_ : α) => y)
    =
    fun (_ : α') => (IsomorphicType.equiv tag) y :=
by
  funext _; simp[isomorph]

variable {α}
variable (β)
theorem proj_rule 
  (x : α)
  : isomorph tag (fun (f : α → β) => f x)
    =
    fun (f : α' → β') => f ((IsomorphicType.equiv tag) x) :=
by
  funext _; simp[isomorph, invIsomorph, IsomorphicType.equiv]
variable {β}

theorem comp_rule 
  (f : β → γ) (g : α → β)
  : isomorph tag (fun x => f (g x))
    =
    fun x => isomorph tag f (isomorph tag g x) := 
by
  funext _; simp[isomorph]

theorem let_rule 
  (f : α → β → γ) (g : α → β)
  : isomorph tag (fun x => let y := g x; f x y)
    =
    fun x' => 
      let y' := isomorph tag g x'
      isomorph tag (fun (xy : α×β) => f xy.1 xy.2) (x', y') := 
by
  funext x'; simp[isomorph, IsomorphicType.equiv, -isomorph.app]

theorem pi_rule 
  (f : α → β → γ) 
  : isomorph tag (fun x y => f x y)
    =
    fun x' => isomorph tag (f ((IsomorphicType.equiv tag).symm x')) := 
by
  funext x'; simp[isomorph, IsomorphicType.equiv]


-- Register `isomorph` as function transformation -------------------------------
--------------------------------------------------------------------------------

set_option linter.unusedVariables false in
open Lean Meta Qq in
def discharger (e : Expr) : SimpM (Option Expr) := return none

open Lean Meta FTrans
def ftransExt : FTransExt where
  ftransName := ``isomorph

  getFTransFun? e := 
    if e.isAppOf ``isomorph then

      if let .some f := e.getArg? 7 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``isomorph then
      e.setArg 7 f
    else          
      e

  idRule  e X := do
    let tag := e.getArg! 4
    tryTheorems
      #[ { proof := ← mkAppOptM ``id_rule #[X, none, tag, none], origin := .decl ``id_rule, rfl := false} ]
      discharger e

  constRule e X y := do
    let tag := e.getArg! 4
    tryTheorems
      #[ { proof := ← mkAppM ``const_rule #[X,tag,y], origin := .decl ``const_rule, rfl := false} ]
      discharger e

  projRule e X i := do
    let tag := e.getArg! 4
    let X' := X.bindingBody!
    if X'.hasLooseBVars then
      trace[Meta.Tactic.ftrans.step] "can't handle this bvar app case, projection rule for dependent function of type {← ppExpr X} is not supported"
      return none
    tryTheorems
      #[ { proof := ← mkAppM ``proj_rule #[X', tag, i], origin := .decl ``proj_rule, rfl := false} ]
      discharger e

  compRule e f g := do
    let tag := e.getArg! 4
    tryTheorems
      #[ { proof := ← withTransparency .all <|
             mkAppM ``comp_rule #[tag, f, g], origin := .decl ``comp_rule, rfl := false} ]
      discharger e

  letRule e f g := do
    let tag := e.getArg! 4
    tryTheorems
      #[ { proof := ← mkAppM ``let_rule #[tag, f, g], origin := .decl ``let_rule, rfl := false} ]
      discharger e

  piRule  e f := do
    let tag := e.getArg! 4
    tryTheorems
      #[ { proof := ← mkAppM ``pi_rule #[tag, f], origin := .decl ``pi_rule, rfl := false} ]
      discharger e

  discharger := discharger


-- register isomorph
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``isomorph, isomorph.ftransExt))


