import Lean

namespace SciLean.Meta.Notation

/--
  Improved function_argument notation that is more organized and consistent.
  
  This notation allows for specifying function arguments in a more structured way,
  making it easier to work with functions that have multiple arguments.
-/

syntax "arg" "(" ident ")" : term

macro_rules
  | `(arg ($x:ident)) => `($x)

/-- Notation for specifying a function argument with a type -/
syntax "arg" "(" ident ":" term ")" : term

macro_rules
  | `(arg ($x:ident : $t:term)) => `($x : $t)

/-- Notation for specifying a function argument with a default value -/
syntax "arg" "(" ident ":=" term ")" : term

macro_rules
  | `(arg ($x:ident := $v:term)) => `($x := $v)

/-- Notation for specifying a function argument with both type and default value -/
syntax "arg" "(" ident ":" term ":=" term ")" : term

macro_rules
  | `(arg ($x:ident : $t:term := $v:term)) => `($x : $t := $v)

-- Example usage
def exampleFunction (arg(x : Nat) arg(y := 10)) : Nat := x + y

#eval exampleFunction 5 -- Should return 15
#eval exampleFunction 5 20 -- Should return 25
#eval "FunctionArgument module loaded successfully"

end SciLean.Meta.Notation
