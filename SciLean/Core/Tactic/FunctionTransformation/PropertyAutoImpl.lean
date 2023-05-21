import SciLean.Tactic.Basic
import SciLean.Core.Tactic.FunctionTransformation.Core
import SciLean.Core.Meta.FunctionProperty.Syntax

namespace SciLean

syntax (noncomp)? defOrAbbrev "∂" bracketedBinder* : argProp
syntax (noncomp)? defOrAbbrev "𝒯" bracketedBinder* : argProp
syntax (noncomp)? defOrAbbrev "∂†" bracketedBinder* : argProp
syntax (noncomp)? defOrAbbrev "ℛ" bracketedBinder* : argProp

macro_rules 
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    $[$nc]? $doa:defOrAbbrev ∂ $extraAssumptions*) => 
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    $[$nc]? $doa:defOrAbbrev ∂ $extraAssumptions* by unfold $id; fun_trans only; clean_up_simp)

macro_rules 
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    $[$nc]? $doa:defOrAbbrev 𝒯 $extraAssumptions*) => 
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    $[$nc]? $doa:defOrAbbrev 𝒯 $extraAssumptions* by unfold $id; fun_trans only; clean_up_simp)

macro_rules 
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    $[$nc]? $doa:defOrAbbrev ∂† $extraAssumptions*) => 
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    $[$nc]? $doa:defOrAbbrev ∂† $extraAssumptions* by unfold $id; fun_trans only; clean_up_simp)

macro_rules 
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    $[$nc]? $doa:defOrAbbrev ℛ $extraAssumptions*) => 
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    $[$nc]? $doa:defOrAbbrev ℛ $extraAssumptions* by unfold $id; fun_trans only; clean_up_simp)
