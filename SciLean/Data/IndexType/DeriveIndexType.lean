import Mathlib.Tactic.ProxyType

import SciLean.Data.IndexType.Basic

namespace SciLean
namespace IndexType

/-! Derive handle for IndexType, done the same

-/

macro "derive_indextype% " t:term : term => `(term| IndexType.ofEquiv _ (proxy_equiv% $t))

open Lean Elab Command in
def mkIndexType (declName : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct declName
  let cmd ← liftTermElabM do
    let header ← Deriving.mkHeader `IndexType 0 indVal
    let binders' ← Deriving.mkInstImplicitBinders ``IndexType indVal header.argNames
    let instCmd ← `(command|
      instance $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
          IndexType $header.targetType := derive_indextype% _)
    return instCmd
  trace[Elab.Deriving.indextype] "instance command:\n{cmd}"
  elabCommand cmd
  return true

open Lean Elab Command in
def mkIndexTypeInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false -- mutually inductive types are not supported
  let declName := declNames[0]!
  mkIndexType declName

open Lean Elab in
initialize
  registerDerivingHandler ``IndexType mkIndexTypeInstanceHandler
  registerTraceClass `Elab.Deriving.indextype
