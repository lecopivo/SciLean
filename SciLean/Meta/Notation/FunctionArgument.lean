import Lean

namespace SciLean.Meta.Notation

/-!
Small helpers for writing *named arguments* in term applications.

This is **not** binder syntax; it is meant to be used in expressions like:

```
f (arg(x := 1)) (arg(y := 2))
```

which expands to `f (x := 1) (y := 2)`.
-/

macro "arg" "(" x:ident ")" : term => `($x)

macro "arg" "(" x:ident ":" t:term ")" : term => `(($x : $t))

-- Example (kept pure: no `#eval` in library code).
def exampleFunction (x : Nat) (y : Nat := 10) : Nat := x + y

end SciLean.Meta.Notation
