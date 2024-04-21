import SciLean.Modules.Geometry.Shape

open FiniteDimensional

namespace SciLean

namespace Shape

variable
  {R : Type _} [RealScalar R] [PlainDataType R]
  {X : Type _} [SemiHilbert R X] [PlainDataType X]
  {Y : Type _} [SemiHilbert R Y]
  {S : Type _} [Shape S X]


variable (R X)
structure Simplex where
  dim : Nat
  points : X^[dim+1]
  hdim : dim = finrank R X
