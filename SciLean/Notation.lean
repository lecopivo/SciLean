import Lean.Parser.Term
import Lean.Parser.Do

open Lean Parser Term

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

