import SciLean.Core.Meta.FunctionProperty.Decl

namespace SciLean

open Lean Parser.Term Lean.Elab Meta

syntax argSpec := ident <|> ("(" ident "," ident,+ ")")

declare_syntax_cat argProp (behavior := both)

syntax "function_property" ident bracketedBinder* (":" term)? "argument" argSpec bracketedBinder* argProp : command

syntax argumentProperties := "argument" argSpec bracketedBinder* argProp,+
syntax "function_properties" ident bracketedBinder* (":" term)? argumentProperties+  : command

macro_rules
| `(function_properties $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec $assumptions:bracketedBinder* $argProp:argProp) => do 
  `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec $assumptions* $argProp:argProp)
| `(function_properties $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec $assumptions:bracketedBinder* $argProp:argProp , $argProps,*) => do 
  `(function_properties $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg $assumptions* $argProp:argProp
    function_properties $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg $assumptions* $argProps:argProp,*)
| `(function_properties $id:ident $parms:bracketedBinder* $[: $retType:term]? $ap:argumentProperties $aps:argumentProperties*) => do 
  `(function_properties $id:ident $parms:bracketedBinder* $[: $retType:term]? $ap
    function_properties $id:ident $parms:bracketedBinder* $[: $retType:term]? $aps:argumentProperties*)


private def argSpecNames (argSpec : TSyntax ``argSpec) : Array Name := 
  match argSpec with 
  | `(argSpec| $id:ident) => #[id.getId]
  | `(argSpec| ($id:ident, $ids:ident,*)) => #[id.getId].append (ids.getElems.map λ id => id.getId)
  | _ => #[]

syntax "funProp" ident ident bracketedBinder* ":=" term : argProp
syntax "funTrans" ident bracketedBinder* ":=" term "by" tacticSeq "by" tacticSeq : argProp

elab_rules : command
| `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec $assumptions1*
    funProp $propId $spaceId $assumptions2* := $proof) => do

  Command.liftTermElabM  do

    Term.elabBinders (parms |>.append assumptions1 |>.append assumptions2) λ contextVars => do

      let propName := propId.getId
      let spaceName := spaceId.getId
  
      let argNames : Array Name := argSpecNames argSpec

      let explicitArgs := (← contextVars.filterM λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)
      let e ← mkAppM id.getId explicitArgs
      let args := e.getAppArgs

      let mainArgIds ← argNames.mapM λ name => do
        let idx? ← args.findIdxM? (λ arg => do
          if let .some fvar := arg.fvarId? then
            let name' ← fvar.getUserName
            pure (name' == name)
          else 
            pure false)
        match idx? with
        | some idx => pure idx
        | none => throwError "Specified argument `{name}` is not valid!"

      let xs := mainArgIds.map λ i => args[i]!

      addFunPropDecl propName spaceName e xs contextVars proof

elab_rules : command
| `(function_property $id $parms* $[: $retType]? 
    argument $argSpec $assumptions1*
    funTrans $transId $assumptions2* := $Tf by $proof by $proof2) => do

  Command.liftTermElabM  do

    Term.elabBinders (parms |>.append assumptions1 |>.append assumptions2) λ contextVars => do

      let transName := transId.getId
  
      let argNames : Array Name := argSpecNames  argSpec 

      let explicitArgs := (← contextVars.filterM λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)
      let e ← mkAppM id.getId explicitArgs
      let args := e.getAppArgs

      let mainArgIds ← argNames.mapM λ name => do
        let idx? ← args.findIdxM? (λ arg => do
          if let .some fvar := arg.fvarId? then
            let name' ← fvar.getUserName
            pure (name' == name)
          else 
            pure false)
        match idx? with
        | some idx => pure idx
        | none => throwError "Specified argument `{name}` is not valid!"

      let xs := mainArgIds.map λ i => args[i]!

      addFunTransDecl transName e xs contextVars Tf proof proof2


syntax " IsSmooth " bracketedBinder* (":=" term)? : argProp

macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec $assumptions1*
    IsSmooth $assumptions2* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``IsSmooth
  let space : Ident := mkIdent ``Vec
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec $assumptions1*
    funProp $prop $space $assumptions2* := $prf)


syntax " IsLin " bracketedBinder* (":=" term)? : argProp

macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    IsLin $extraAssumptions* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``IsLin
  let space : Ident := mkIdent ``Vec
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    funProp $prop $space $extraAssumptions* := $prf)


syntax " HasAdjoint " bracketedBinder* (":=" term)? : argProp

macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    HasAdjoint $extraAssumptions* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``HasAdjoint
  let space : Ident := mkIdent ``SemiHilbert
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    funProp $prop $space $extraAssumptions* := $prf)


syntax " HasAdjDiff " bracketedBinder* (":=" term)? : argProp

macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    HasAdjDiff $extraAssumptions* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``HasAdjDiff
  let space : Ident := mkIdent ``SemiHilbert
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    funProp $prop $space $extraAssumptions* := $prf)
