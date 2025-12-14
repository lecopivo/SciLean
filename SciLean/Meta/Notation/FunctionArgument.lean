import Lean

namespace SciLean.Meta.Notation

/-!
Small helpers for writing function arguments uniformly in term applications.

This is **not** binder syntax; it is meant to be used in expressions like:

```
f (arg(x)) (arg(y : Nat))
```

which expands to `f x (y : Nat)`.

Note: named-argument forms like `(x := v)` only parse in *application argument position*
in Lean (they are not general terms), so we intentionally do not provide `arg(x := v)` here.
-/

macro "arg" "(" x:ident ")" : term => `($x)

macro "arg" "(" x:ident ":" t:term ")" : term => `(($x : $t))

-- Example (kept pure: no `#eval` in library code).
def exampleFunction (x : Nat) (y : Nat := 10) : Nat := x + y

end SciLean.Meta.Notation
