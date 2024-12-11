import SciLean.Analysis.SpecialFunctions.Gaussian

namespace SciLean


variable
  {R} [RealScalar R]
  {C} [Scalar R C]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] {d : outParam ℕ} [hdim : Dimension R X d]

set_default_scalar C

open Scalar

instance [Scalar R C] : HSMul R C C :=
  ⟨fun x y => make (x * real y) (x * imag y)⟩


notation "ⅈ" => Scalar.make (K:=defaultScalar%) 0 1


def gaborWavelet (σ : R) (k : X) (x : X) :=
  exp (- ‖x‖₂²[R]/(2*σ^2)) • exp (-(⟪k,x⟫[R])•ⅈ)






open ComplexConjugate
