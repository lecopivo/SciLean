import SciLean.Meta.SimpAttr

import Mathlib.Data.FunLike.Basic -- this import does not seem to be enough
import Mathlib.Logic.Equiv.Defs

namespace Scilean

open Lean Meta in
/-- Zeta delta reduction for bundled morphisms/DFunLike.coe.

Expressions of the form `DFunLike.coe fVar x` where `fVar` is free variable with value `fVal` are
replaced with `DFunLike.coe fVal x`.

For examples, this
```
let f : R →*+ R := Ring.id
⇑f x
```
reduces to
```
⇑Ring.id x
```
-/
simproc_decl dfunlike_coe_zetaDelta (DFunLike.coe _ _) := fun e => do
  let x := e.appArg!
  let .fvar fId := e.appFn!.appArg! | return .continue
  let .some f ← fId.getValue? | return .continue
  let coe := e.appFn!.appFn!
  return .visit { expr := coe.app f |>.app x }

attribute [simp, simp_core] dfunlike_coe_zetaDelta
