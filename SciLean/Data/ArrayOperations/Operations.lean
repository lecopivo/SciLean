import SciLean.Data.ArrayOperations.Basic
import SciLean.Data.IndexType

namespace SciLean

namespace ArrayOps

variable {coll idx elem : Type*} [IndexType idx]
  [GetElem' coll idx elem]
  [SetElem' coll idx elem]

def mapMono [DefaultIndex coll idx] (f : elem → elem) (xs : coll) : coll :=
  IndexType.foldl (init:=xs) (fun xs (i : idx) =>
    let xi := xs[i]
    let xi' := f xi
    setElem xs i xi' .intro)

def mapIdxMono (f : idx → elem → elem) (xs : coll) : coll :=
  IndexType.foldl (init:=xs) (fun xs (i : idx) =>
    let xi := xs[i]
    let xi' := f i xi
    setElem xs i xi' .intro)
