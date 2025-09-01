namespace SciLean

/-- `holdLet` is just identity function with a special support from some tactics.

Tactics like `autodiff`, `lsimp`, `lfun_trans` inline let bindings of functions, for examples
```
let f := fun x => x*x
f 2
```
would get simplified to `2*2` even with option `zeta:=false`. This reduction is important for
reverse mode AD.

Function `holdLet` is useful for preventing this reduction, so adding `holdLet`
```
let f := holdLet <| fun x => x*x
f 2
```
will prevent `lsimp` to remove the let.  -/
@[inline]
def holdLet {α : Type u} (a : α) := a
