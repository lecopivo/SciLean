import SciLean.Data.VectorType.Base
import SciLean.Data.IndexType.IndexInclusion

namespace SciLean

open VectorType Classical

/-- `Subector X X' ι` says that `X'` is subvector of `X` and provides bunch of operations
on `X` modifying only `X'` part of it. -/
class SubvectorType
      (X : outParam (Type*)) (X' : Type*)
      {n n' : Type*} {_ : IndexType n} {_ : IndexType n'}
      (ι : {f : n' → n // f.Injective })
      {R K} {_ : RealScalar R} {_ : Scalar R K}
      [VectorType.Base X n K] [VectorType.Base X' n' K]
  where

    subvector (x : X) : X'
    subvector_spec (x : X) (i' :n') :
      (subvector x)[i']
      =
       x[ι.1 i']

    /-- Modify part of `x` with -/
    axpby (a : K) (x' : X') (b : K) (x : X) : X
    axpby_spec (a : K) (x' : X') (b : K) (x : X) (i : n) :
      (axpby a x' b x)[i]
      =
      if h : ∃ (i' : n'), ι.1 i' = i then
         let i' := choose h
         a • (x'[i']) + b • (x[ι.1 i'])
      else
         x[i]
