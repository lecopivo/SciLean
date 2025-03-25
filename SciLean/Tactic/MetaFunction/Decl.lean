import Lean
import SciLean.Tactic.DataSynth.Elab
import SciLean.Tactic.DataSynth.Attr

open Lean Meta

namespace SciLean.Tactic.MetaFun

/--
Meta function declaration

Stores information about the meta-function and its corresponding proposition

-/
structure MetaFunDecl where
  metaFunName : Name
  metaFunPropName : Name
deriving Inhabited

/--
Maps that map:
  - meta-function name to meta-function declaration
  - meta-function proposition name to meta-function declaration
-/
structure MetaFunDeclMaps where
  funToDecl  : NameMap MetaFunDecl
  propToDecl : NameMap MetaFunDecl
deriving Inhabited

/--
Environment extension storing all meta-functions
-/
abbrev MetaFunExt := SimpleScopedEnvExtension MetaFunDecl MetaFunDeclMaps


/--
Environment extension storing all meta-functions
-/
initialize metaFunExt : MetaFunExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := ⟨{},{}⟩
    addEntry := fun d e =>
      {d with funToDecl := d.funToDecl.insert e.metaFunName e
              propToDecl := d.funToDecl.insert e.metaFunPropName e}
  }


def getDeclFromFun? (n : Name) : CoreM (Option MetaFunDecl) := do
  return (metaFunExt.getState (← getEnv)).funToDecl.find? n

def getDeclFromProp? (n : Name) : CoreM (Option MetaFunDecl) := do
  return (metaFunExt.getState (← getEnv)).funToDecl.find? n



open Lean Elab Command
/--
Define new meta-function, these functions are non-computable functions satisfying certain property.
These meta-functions can be evaluated only on meta programming level by syntactically inspecting
their arguments.

For example:
```
variable {α : Type} [LinearOrder α] [Inhabited α]

meta_fun_decl bounds (x : α) : α×α
satisfying
  bounds.1 ≤ x ∧ x ≤ bounds.2
```
defines a function `bounds (x : α) : α×α` which returns lower and upper bound of `x`.

There can be many bounds and the idea behing this meta-function is that it will return the best
effort bounds based on the syntactic structure of `x`.

-/

elab "meta_fun_decl" id:ident bs:bracketedBinder* ":" ty:term "satisfying" prop:term : command => do

  let structId := mkIdent id.getId.capitalize
  elabCommand (← `(command|
    @[data_synth out $id]
    structure $structId $bs* ($id : $ty) where
      prop : $prop))

  elabCommand (← `(command| opaque $id $bs* : $ty))

  let decl : MetaFunDecl := {
    metaFunName := id.getId
    metaFunPropName := structId.getId
  }

  metaFunExt.add decl



open Lean Elab Term in
/--
Evaluate meta-function
-/
elab "#eval_meta_fun" x:term : command => do
  runTermElabM fun _ => do
  let x ← elabTerm x none

  let (fName, args) := x.getAppFnArgs

  let .some decl ← getDeclFromFun? fName
    | throwError m!"{x} is not application of meta-function"

  let prop ← mkAppOptM decl.metaFunPropName (args.map Option.some)
  let (xs,_,_) ← forallMetaTelescope (← inferType prop)
  let prop := prop.beta xs

  let .some goal ← Tactic.DataSynth.isDataSynthGoal? prop
    | throwError m!"{decl.metaFunPropName} is not well defined meta-function, this is likely a bug"

  let .some result ← (Tactic.DataSynth.dataSynth goal).runInMetaM
    | throwError m!"failed to evaluate meta-function {x}"

  logInfo result.xs[0]!
