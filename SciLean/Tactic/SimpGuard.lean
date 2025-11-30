import Lean

namespace SciLean.Tactic

open Lean Meta Elab Tactic

/--
  A guard for simp theorems to prevent them from applying to themselves.
  
  This is an alternative to the `hold` trick currently used in SciLean.
  It allows specifying that a simp theorem applies only if a certain function
  does not unify to identity.
-/

def guardedSimpCore (guard : Expr → MetaM Bool) (e : Expr) : MetaM (Option Expr) := do
  if !(← guard e) then
    return none
  else
    -- Apply the actual simplification
    return some e

syntax (name := guardedSimpAttr) "guarded_simp" ident : attr

/-- Register a guarded simp theorem -/
@[macro guardedSimpAttr] def registerGuardedSimpAttr : Macro
  | `(attr| guarded_simp $id:ident) => do
    let name := id.getId
    `(attribute [simp] $id:ident)
  | _ => Macro.throwUnsupported

/-- Guard that prevents a simp theorem from applying to identity functions -/
def notIdentityGuard (e : Expr) : MetaM Bool := do
  let f := e.getAppFn
  if f.isConst && f.constName == ``id then
    return false
  else
    return true

end SciLean.Tactic
