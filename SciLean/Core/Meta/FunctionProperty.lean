import Lean.Parser

import SciLean.Prelude
import SciLean.Data.Prod
import SciLean.Core.Meta.BracketedBinder

namespace SciLean

open Lean Parser.Term 

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

