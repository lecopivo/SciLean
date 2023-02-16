import Lean
import Lean.Parser.Do
import Lean.Parser.Term

open Lean Parser

namespace SciLean

--- Syntax for: x += y, x -= y, x *= y
syntax atomic(Term.ident Term.optType) " += " term : doElem
syntax atomic(Term.ident Term.optType) " -= " term : doElem
syntax atomic(Term.ident Term.optType) " *= " term : doElem
syntax atomic(Term.ident Term.optType) " *.= " term : doElem
syntax atomic(Term.ident Term.optType) " /= " term : doElem

--- Rules for: x += y, x -= y, x *= y
macro_rules
| `(doElem| $x:ident $[: $ty]? += $e) => `(doElem| $x:ident $[: $ty]? := $x:ident + $e)
macro_rules
| `(doElem| $x:ident $[: $ty]? -= $e) => `(doElem| $x:ident $[: $ty]? := $x:ident - $e)
macro_rules
| `(doElem| $x:ident $[: $ty]? *= $e) => `(doElem| $x:ident $[: $ty]? := $x:ident * $e)
macro_rules
| `(doElem| $x:ident $[: $ty]? *.= $e) => `(doElem| $x:ident $[: $ty]? := $e * $x:ident)
macro_rules
| `(doElem| $x:ident $[: $ty]? /= $e) => `(doElem| $x:ident $[: $ty]? := $x:ident / $e)



--------------------------------------------------------------------------------

open Elab Term Meta


class Partial {α : Sort u} (a : α) {β : outParam $ Sort v} (b : outParam β)

elab:max "∂" x:term:max : term => withFreshMacroScope do
  _ ← synthInstance (← elabType (← `(Partial $x ?m)))
  elabTerm (← `(?m)) none


class PartialDagger {α : Sort u} (a : α) {β : outParam $ Sort v} (b : outParam β)

elab:max "∂†" x:term:max : term => withFreshMacroScope do
  _ ← synthInstance (← elabType (← `(PartialDagger $x ?m)))
  elabTerm (← `(?m)) none


class Differential {α : Sort u} (a : α) {β : outParam $ Sort v} (b : outParam β)

elab:max "ⅆ" x:term:max : term => withFreshMacroScope do
  _ ← synthInstance (← elabType (← `(Differential $x ?m)))
  elabTerm (← `(?m)) none


class Nabla {α : Sort u} (a : α) {β : outParam $ Sort v} (b : outParam β)

elab:max "∇" x:term:max : term => withFreshMacroScope do
  _ ← synthInstance (← elabType (← `(Nabla $x ?m)))
  elabTerm (← `(?m)) none


class TangentMap {α : Sort u} (a : α) {β : outParam $ Sort v} (b : outParam β)

elab:max "𝒯" x:term:max : term => withFreshMacroScope do
  _ ← synthInstance (← elabType (← `(TangentMap $x ?m)))
  elabTerm (← `(?m)) none


class ReverseDifferential {α : Sort u} (a : α) {β : outParam $ Sort v} (b : outParam β)

elab:max "ℛ" x:term:max : term => withFreshMacroScope do
  _ ← synthInstance (← elabType (← `(ReverseDifferential $x ?m)))
  elabTerm (← `(?m)) none



class OTimes {α : Sort u} {β : Sort v} (a : α) (b : β) {γ : outParam $ Sort w} (c :  outParam γ) 

elab x:term:71 "⊗" y:term:72 : term => withFreshMacroScope do
  _ ← synthInstance (← elabType (← `(OTimes $x $y ?m)))
  elabTerm (← `(?m)) none



class Integral {α : Sort u} (a : α) {β : outParam $ Sort v} (b : outParam β)

elab:max "∫" x:term:max : term => withFreshMacroScope do
  _ ← synthInstance (← elabType (← `(Integral $x ?m)))
  elabTerm (← `(?m)) none

