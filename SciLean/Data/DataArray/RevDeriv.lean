import SciLean.Data.DataArray.DataArray
import SciLean.Data.ArrayType.Algebra
import SciLean.Analysis.Calculus.RevFDerivProj

namespace SciLean


/-- When we run reverse mode derivative w.r.t to an array we switch to optimized(but experimental)
version of reverse mode derivative that should yield much more performant code. -/
@[simp ↓ high, simp_core ↓ high]
theorem revFDeriv_on_DataArrayN
  {R : Type} [RCLike R]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [PlainDataType X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]
  {I : Type} [IndexType I]
  (f : DataArrayN X I → Y)  :
  revFDeriv R f
  =
  fun x =>
    let ydf := revFDerivProj R Unit f x
    (ydf.1, ydf.2 ()) := by unfold revFDerivProj revFDeriv; simp
