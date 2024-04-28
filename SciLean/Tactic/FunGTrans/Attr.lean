import SciLean.Tactic.FunGTrans.Theorems
import SciLean.Tactic.FunGTrans.Decl

open Lean Meta

namespace SciLean.Tactic.FunGTrans


/-- Initialization of `funProp` attribute -/
initialize funPropAttr : Unit ←
  registerBuiltinAttribute {
    name  := `gtrans
    descr := "generalized transformation"
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName _stx attrKind =>
       discard <| MetaM.run do
       let info ← getConstInfo declName

       forallTelescope info.type fun _ b => do
         if b.isProp then
           addGTransDecl declName
         else
           addTheorem declName attrKind
    erase := fun _declName =>
      throwError "can't remove `gtrans` attribute (not implemented yet)"
  }
