import SciLean.Data.ArrayOperations.Basic
import SciLean.Data.IndexType
import SciLean.Data.IndexType.Basic
import SciLean.Data.IndexType.Fold

namespace SciLean

namespace ArrayOps

variable {X I Y : Type*} {nI} [IndexType I nI] [Fold I]
  [GetElem' X I Y]
  [SetElem' X I Y]

/--
Maps elements of `xs` by `f` with data accessor `g`.

```
(mapIdxMono2 f g xs)[i] = f i (g i) x[i]
```

This is a low level function that provides additional agument `g` which is used as data accessor
inside of `f`. For example, instead of writing
```
def add (x y : X) := mapIdxMono (fun i xi => xi + y[i]) x
```
you should write
```
def add (x y : X) := mapIdxMono2 (fun i yi xi => xi + yi) (fun i => y[i]) x
```
This way reverse mode AD can produce better code.

An example of higer arity function
```
def mulAdd (x y z : X) := mapIdxMono2 (fun i (xi,yi) zi => xi*yi + zi) (fun i => (x[i],y[i])) z
```
-/
@[inline, specialize, macro_inline]
def mapIdxMonoAcc (f : I → Z → Y → Y) (g : I → Z) (xs : X) : X :=
  IndexType.fold (init:=xs) .full (fun (i : I) xs  =>
    let xi := xs[i]
    let yi := g i
    let xi' := f i (g i) xi
    setElem xs i xi' .intro)


/--
Maps elements of `xs` by `f`.

```
(mapIdxMono2 f xs)[i] = f i x[i]
```

Note: Consider using `mapIdxMono2` if `f` is accesing element of another array,
      like `f := fun i xi => xi + y[i]`. Reverse mode AD is able to produce better gradients for
      `mapIdxMono2`.
-/
@[reducible, inline, specialize, macro_inline]
def mapIdxMono (f : I → Y → Y) (xs : X) : X :=
  mapIdxMonoAcc (fun i _ y => f i y) (fun _ => ()) xs


/--
Maps elements of `xs` by `f`.

```
(mapIdxMono2 f xs)[i] = f x[i]
```
-/
@[reducible, inline, specialize, macro_inline]
def mapMono [DefaultIndex X I] (f : Y → Y) (xs : X) : X :=
  mapIdxMono (fun _ : I => f) xs
