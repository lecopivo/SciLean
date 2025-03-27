
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Erased

import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.Normed.IsContinuousLinearMap
import SciLean.Analysis.SpecialFunctions.Inner

namespace SciLean


/--
Tage type to indicate what implementation of tensor product we want.

Because tensor product is usually implemented with matrices/tensors we have two main tags
`dense` and `sparse`. To make keep this user extensible we also support `custom n`.

TODO: TensorProductType should accept this as an input
 -/
inductive TansorProductTag where
  | dense
  | sparse
  | custom (name : Name)

open TensorProduct  in
/-- `TensorProductType R Y X YX` says that `YX` is mathematical tensor product `Y ⊗ X`.

When the default scalar type it not set you have to write `X ⊗[R] Y`

Example:
```
Float^[m] ⊗ Float^[n] = Float^[m,n]
Float^[m] ⊗ Float     = Float^[m]
    Float ⊗ Float^[n] = Float^[n]
(Float^[m] × Float^[n]) ⊗ Float^[k] = Float^[m,k] × Float^[n,k]
```

Because we consider tensor product only on inner product spaces we identify `Dual R X` with `X` and
because `(Y ⊗ Dual R X) ≃ (X →L[R] Y)` we consider elements of `(Y ⊗ X)` as linear maps.
Thus this class also provides matrix-vector multiplication `matVecMulAdd` and vector-matrix
multiplication `vecMatMulAdd` (when we identity `Dual R Y` with `Y`).
-/
class TensorProductType (R Y X : Type*) (YX : outParam Type*) [RCLike R]
  [NormedAddCommGroup Y] [AdjointSpace R Y] [NormedAddCommGroup X] [AdjointSpace R X]
  [AddCommGroup YX] [Module R YX]
  where
    /-- Equivalence between the computational tensor product `YX` and the mathematical `Y ⊗ X`

    It is marked as `Erased` as many mathlib functions about the tensor product are noncomputable. -/
    equiv : Erased (YX ≃ₗ[R] (Y ⊗[R] X))

    /-- Outer/tensor product of two vectors added to a matrix

    ```
    tmulAdd a y x A = a•y*xᴴ + A
    ```
    -/
    tmulAdd (a : R) (y : Y) (x : X) (A : YX) : YX

    tmulAdd_eq_tmul : ∀ r x y A,
      tmulAdd r y x A
      =
      equiv.out.symm (r • (y ⊗ₜ[R] x) + equiv.out A)


    /-- Matrix vector multiplication
    ```
    matVecMul a A x b y = a•A*x + b•y
    ```
    -/
    matVecMulAdd (a : R) (A : YX) (x : X) (b : R) (y : Y) : Y


    /-- Vector matrix multiplication
    ```
    vecMatMulAdd a y A b x = a•y*A + b•x
    ```
    -/
    vecMatMulAdd (a : R) (y : Y) (A : YX) (b : R) (x : X) : X


export TensorProductType (tmulAdd matVecMulAdd vecMatMulAdd)

/-- Tag class used to obtain the canonical tensor product type of `Y` and `X` -/
class TensorProductGetYX (R Y X : Type*) (YX : outParam Type*)

/-- Tag class used to obtain the output type `Y` of matrix multiplication `Y ⊗ X → X → Y` -/
class TensorProductGetY (R Y : outParam Type*) (X YX : Type*)

/-- Tag class used to obtain the output type `X` of transposed matrix multiplication `Y ⊗ X → Y → X` -/
class TensorProductGetX (R : outParam Type*) (Y : Type*) (X : outParam Type*) (YX : Type*)

/-- Tag class to infer `R`,`X` and `Y` from `YX = Y ⊗[R] X`.

Together with `TensorProductGetYX` it is use to infer the result type of matrix-matrix
multiplication -/
class TensorProductGetRXY (R Y X : outParam Type*) (YX : Type*)


open TensorProductType in
/-- Outer/tensor product of two vectors. -/
def tmul
    (R : Type*) {Y X : Type*} {YX : Type*}
    [RCLike R]
    [NormedAddCommGroup Y] [AdjointSpace R Y]
    [NormedAddCommGroup X] [AdjointSpace R X]
    [AddCommGroup YX] [Module R YX]
    [TensorProductType R Y X YX]
    (y : Y) (x : X) : YX :=
  tmulAdd (1:R) y x 0


----------------------------------------------------------------------------------------------------
-- Notation ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


open Lean Elab Term Meta Qq in
elab (priority:=high) x:term:101 " ⊗[" R:term "] " y:term:100 : term => do

  let xType ← inferType (← elabTerm x none)
  let yType ← inferType (← elabTerm y none)

  if xType.isSort ∧ yType.isSort then

    let cls ← elabTerm (← `(TensorProductType $R $x $y _)) none
    let _ ← synthInstance cls

    return cls.getArg! 3
  else
    let cls ← elabTerm (← `(TensorProductType $R (type_of% $x) (type_of% $y) _)) none
    let _ ← synthInstance? cls

    let t ← elabTerm  (← `(tmul $R $x $y)) (cls.getArg! 3)
    return t

macro (priority:=high) x:term:101 " ⊗ " y:term:100 : term => `($x ⊗[defaultScalar%] $y)

@[app_unexpander tmul] def unexpandTMul : Lean.PrettyPrinter.Unexpander
  | `($(_) $_ $y $x) => `($y ⊗ $x)
  | _ => throw ()




----------------------------------------------------------------------------------------------------
-- Instances ---------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section Identity
variable {R : Type*} [RCLike R]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X]


-- TODO: !!!Fix this for complex `R`!!! it is missing complex conjugates
open ComplexConjugate
instance tpScalarLeft : TensorProductType R R X X where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd a x y A := a•(x•y) + A
  matVecMulAdd a A x b y := a*⟪A,x⟫[R] + b*y
  vecMatMulAdd a y A b x := a•(star y•A) + b • x
  tmulAdd_eq_tmul := sorry_proof

-- this creates a diamond with the previous for `ttmul` on `R ⊗'[R] R`
-- what to do about this?
-- TODO: !!!Fix this for complex `R`!!! it is missing complex conjugates
open MulOpposite in
instance (priority:=low) tpScalarRight
  [Module (Rᵐᵒᵖ) X] [Star X] :
  TensorProductType R X R X where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd a x y A := a•(op y•x) + A
  matVecMulAdd a A y b x := a•(op y • star A) + b • x
  vecMatMulAdd a x A b y := a*⟪x,A⟫[R] + b*y
  tmulAdd_eq_tmul := sorry_proof

instance {R} [RCLike R] : TensorProductGetYX R R X X := ⟨⟩
instance {R} [RCLike R] : TensorProductGetYX R X R X := ⟨⟩

example : (tpScalarLeft : TensorProductType R R R R)
          =
          (tpScalarRight : TensorProductType R R R R) := by rfl

@[simp, simp_core]
theorem tmul_scalar_left (a : R) (x : X) :
  a ⊗[R] x = a • x := by simp[tmul,tmulAdd]

open MulOpposite in
@[simp, simp_core]
theorem tmul_scalar_right [Module (Rᵐᵒᵖ) X] [Star X] (a : R) (x : X) :
  x ⊗[R] a = (op a) • x := by simp[tmul,tmulAdd]

end Identity


----------------------------------------------------------------------------------------------------
-- Simps -------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section Simps

variable
  {R Y X YX : Type*} [RCLike R]
  [NormedAddCommGroup Y] [AdjointSpace R Y] [NormedAddCommGroup X] [AdjointSpace R X]
  [AddCommGroup YX] [Module R YX]
  [TensorProductType R Y X YX]

@[simp, simp_core]
theorem tmul_zero (y : Y) : y ⊗[R] (0 : X) = 0 := by sorry_proof

@[simp, simp_core]
theorem zero_tmul (x : X) : (0 : Y) ⊗[R] x = 0 := by sorry_proof

@[simp, simp_core]
theorem matVecMulAdd_zero_a (b : R) (A : YX) (x : X) (y : Y) :
    matVecMulAdd 0 A x b y = b•y := by sorry_proof

@[simp, simp_core]
theorem matVecMulAdd_zero_A (a b : R) (x : X) (y : Y) :
    matVecMulAdd a (0 : YX) x b y = b•y := by sorry_proof

@[simp, simp_core]
theorem matVecMulAdd_zero_x (a b : R) (A : YX) (y : Y) :
    matVecMulAdd a A (0:X) b y = b•y := by sorry_proof

@[simp, simp_core]
theorem vecMatMulAdd_zero_a (b : R) (A : YX) (x : X) (y : Y) :
    vecMatMulAdd 0 y A b x = b•x := by sorry_proof

@[simp, simp_core]
theorem vecMatMulAdd_zero_A (a b : R) (x : X) (y : Y) :
  vecMatMulAdd a y (0 : YX) b x = b•x := by sorry_proof

@[simp, simp_core]
theorem vecMatMulAdd_zero_y (a b : R) (A : YX) (x : X) :
  vecMatMulAdd a (0:Y) A b x = b•x := by sorry_proof
