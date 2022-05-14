import Lean.Parser.Term
import Lean.Parser.Do

open Lean Parser Term

--- Syntax for: x += y, x -= y, x *= y
syntax atomic(Term.ident Term.optType) " += " term : doElem
syntax atomic(Term.ident Term.optType) " -= " term : doElem
syntax atomic(Term.ident Term.optType) " *= " term : doElem
syntax atomic(Term.ident Term.optType) " *.= " term : doElem
syntax atomic(Term.ident Term.optType) " /= " term : doElem

--- Syntax for: x[i] := y, x[i] += y, x[i] -= y, x[i] *= y
syntax (priority := high) atomic(Lean.Parser.Term.ident) noWs "[" term "]" " := " term : doElem
syntax (priority := high) atomic(Lean.Parser.Term.ident) noWs "[" term "]" " ← " term : doElem
syntax atomic(Term.ident) noWs "[" term "]" " += " term : doElem
syntax atomic(Term.ident) noWs "[" term "]" " -= " term : doElem
syntax atomic(Term.ident) noWs "[" term "]" " *= " term : doElem
syntax atomic(Term.ident) noWs "[" term "]" " *.= " term : doElem
syntax atomic(Term.ident) noWs "[" term "]" " /= " term : doElem

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

--- Rules for: x[i] := y, x[i] += y, x[i] -= y, x[i] *= y
macro_rules
| `(doElem| $x:ident[ $i:term ] := $xi) => `(doElem| $x:ident := ($x:ident).set $i $xi)
macro_rules
| `(doElem| $x:ident[ $i:term ] ← $xi) => `(doElem| $x:ident := ($x:ident).set $i (← $xi))
macro_rules
| `(doElem| $x:ident[ $i:term ] += $xi) => `(doElem| $x:ident := ($x:ident).modify $i (λ val => val + $xi))
macro_rules
| `(doElem| $x:ident[ $i:term ] -= $xi) => `(doElem| $x:ident := ($x:ident).modify $i (λ val => val - $xi))
macro_rules
| `(doElem| $x:ident[ $i:term ] *= $xi) => `(doElem| $x:ident := ($x:ident).modify $i (λ val => val * $xi))
macro_rules
| `(doElem| $x:ident[ $i:term ] *.= $xi) => `(doElem| $x:ident := ($x:ident).modify $i (λ val => $xi * val))
macro_rules
| `(doElem| $x:ident[ $i:term ] /= $xi) => `(doElem| $x:ident := ($x:ident).modify $i (λ val => val / $xi))
