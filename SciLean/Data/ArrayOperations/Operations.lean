import SciLean.Data.ArrayOperations.Basic
import SciLean.Data.IndexType
import SciLean.Data.IdxType.Basic
import SciLean.Data.IdxType.Fold

namespace SciLean

namespace ArrayOps

variable {coll idx elem : Type*} {n} [IdxType idx n] [IdxType.Fold' idx]
  [GetElem' coll idx elem]
  [SetElem' coll idx elem]

@[inline]
def mapMono [DefaultIndex coll idx] (f : elem → elem) (xs : coll) : coll :=
  IdxType.fold (init:=xs) .full (fun (i : idx) xs =>
    let xi := xs[i]
    let xi' := f xi
    setElem xs i xi' .intro)

@[inline]
def mapIdxMono (f : idx → elem → elem) (xs : coll) : coll :=
  IdxType.fold (init:=xs) .full (fun (i : idx) xs  =>
    let xi := xs[i]
    let xi' := f i xi
    setElem xs i xi' .intro)
