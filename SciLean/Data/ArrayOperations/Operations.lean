import SciLean.Data.ArrayOperations.Basic
import SciLean.Data.IndexType
import SciLean.Data.IdxType.Basic
import SciLean.Data.IdxType.Fold

namespace SciLean

namespace ArrayOps

variable {coll idx elem : Type*} {n} [IdxType idx n] [IdxType.Fold' idx]
  [GetElem' coll idx elem]
  [SetElem' coll idx elem]

@[inline,specialize]
def mapIdxMono (f : idx → elem → elem) (xs : coll) : coll :=
  IdxType.fold (init:=xs) .full (fun (i : idx) xs  =>
    let xi := xs[i]
    let xi' := f i xi
    setElem xs i xi' .intro)


-- this version should be used if we access some other data with the index. This data access should
-- be done through `g`
@[inline,specialize]
def mapIdxMono2 (f : idx → Z → elem → elem) (g : idx → Z) (xs : coll) : coll :=
  IdxType.fold (init:=xs) .full (fun (i : idx) xs  =>
    let xi := xs[i]
    let yi := g i
    let xi' := f i (g i) xi
    setElem xs i xi' .intro)

@[inline,specialize]
abbrev mapMono [DefaultIndex coll idx] (f : elem → elem) (xs : coll) : coll :=
  mapIdxMono (fun _ : idx => f) xs
