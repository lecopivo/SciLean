import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Erased

import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.Normed.IsContinuousLinearMap
import SciLean.Analysis.SpecialFunctions.Inner
import SciLean.Data.DataArray.MatrixType

import SciLean.Tactic.SimpleProxyType
import SciLean.Data.Instances.Sigma

namespace SciLean

-- todo move this
open NormedSpace in
def AdjointSpace.toDual (𝕜 : Type u_1) {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E] [AdjointSpace 𝕜 E]
  (x : E) : Dual 𝕜 E := fun x' =>L[𝕜] ⟪x,x'⟫[𝕜]


/--
Tage type to indicate what implementation of tensor product we want.

Because tensor product is usually implemented with matrices/tensors we have two main tags
`dense` and `sparse`. To make keep this user extensible we also support `custom n`.
 -/
inductive TansorProductTag where
  | dense
  | sparse
  | custom (name : Name)

open TensorProduct NormedSpace AdjointSpace in
/-- `X ⊗' Y` is tensor product of `X` and `Y`.

Mathematically the same as `X ⊗ Y` (without the dash) but `X ⊗' Y` has efficient computatinal
representation.

When the default scalar type it not set you have to write `X ⊗'[R] Y`

Example:
```
Float^[m] ⊗' Float^[n] = Float^[m,n]
Float^[m] ⊗' Float     = Float^[m]
    Float ⊗' Float^[n] = Float^[n]
```-/
class TensorProductType (R Y X YX : Type*) [RCLike R]
  [NormedAddCommGroup Y] [AdjointSpace R Y] [NormedAddCommGroup X] [AdjointSpace R X]
  [AddCommGroup YX] [Module R YX]
  where
    /-- Equivalence between the computational tensor product `XY` and the mathematical `X ⊗ Y`

    It is marked as `Erased` as many mathlib functions about the tensor product are noncomputable. -/
    -- NOTE: maybe `Y` should be dual here as `X ⊗' Y` should behave like matrices !!!
    equiv : Erased (YX ≃ₗ[R] (Y ⊗[R] Dual R X))

    /-- Outer/tensor product of two vectors added to a matrix

    ```
    tmulAdd' a y x A = a•y*xᴴ + A
    ```
    -/
    tmulAdd (a : R) (y : Y) (x : X) (A : YX) : YX

    tmulAdd_eq_tmul : ∀ r x y A,
      tmulAdd r y x A
      =
      equiv.out.symm (r • (y ⊗ₜ[R] toDual R x) + equiv.out A)


    /-- Matrix vector multiplication
    ```
    matVecMul a A x b y = a•A*x + b•y
    ```
    -/
    matVecMulAdd (a : R) (A : YX) (x : X) (b : R) (y : Y) : Y


    /-- Conjugate/transpose matrix vector multiplication
    ```
    vecMul a A y b x = a•Aᴴ*y + b•x
    ```
    -/
    matHVecMulAdd (a : R) (A : YX) (y : Y) (b : R) (x : X) : X


export TensorProductType (tmulAdd matVecMulAdd matHVecMulAdd)

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
abbrev tmul
    (R : Type*) {Y X : Type*} {YX : Type*} [TensorProductGetYX R Y X YX] -- infer `YX` from R X and Y
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

/-- Notation class for tensor multiplication `⊗` over ring `R`

It is defined in this way, unlike `HAdd`, to support tensor product of elements and types at the same
time.
 -/
class TMul (R : Type*) {α β : Sort*} {γ : outParam Sort*} (a : α) (b : β) (c : outParam γ) where

/--
Notation instance for tensor multiplication of two types.

To infer the tensor type we use the tag class `TensorProductGetYX`.
 -/
instance (R Y X YX : Type*) [TensorProductGetYX R Y X YX]
    [RCLike R]
    [NormedAddCommGroup Y] [AdjointSpace R Y]
    [NormedAddCommGroup X] [AdjointSpace R X]
    [AddCommGroup YX] [Module R YX]
    [TensorProductType R Y X YX] :
    TMul R Y X YX := ⟨⟩

/--
Notation instance for tensor multiplication of two elements.

To infer the tensor type we use the tag class `TensorProductGetYX`.
 -/
instance (R Y X YX : Type*) [TensorProductGetYX R Y X YX] -- infer `YX` from R X and Y
    [RCLike R]
    [NormedAddCommGroup Y] [AdjointSpace R Y]
    [NormedAddCommGroup X] [AdjointSpace R X]
    [AddCommGroup YX] [Module R YX]
    [TensorProductType R Y X YX]
    (y : Y) (x : X) :
    TMul R y x (tmul R y x) := ⟨⟩

open Lean Meta Elab Term in
/-- Outer/tensor product of vectors or types.

For types:
`R^[m] ⊗ R^[n]` is equal to `R^[m,n]`.

For vectors, `x : R^[m]` and `y : R^[n]`
`x ⊗ y` is outer product resulting in `m×n` matrix.
 -/
elab (name:=tmulSyntax) x:term:101 " ⊗[" R:term "]" y:term:100 : term => do
    let tp ← elabTerm (← `(TMul $R $x $y _)) none
    let _ ← synthInstance tp
    return (tp.appArg!)


@[inherit_doc tmulSyntax]
macro:100 x:term:101 " ⊗ " y:term:100 : term => `($x ⊗[defaultScalar%] $y)

@[app_unexpander tmul] def unexpandTMul : Lean.PrettyPrinter.Unexpander
  | `($(_) $_ $y $x) => `($y ⊗ $x)
  | _ => throw ()



----------------------------------------------------------------------------------------------------
-- Vector-matrix multiplication --------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open TensorProductType in
/-- Matrix vector multiplication instances.

We use tag class `TensorProductGetY` to infer the product output type `Y` and ring `R` -/
instance (R Y X YX : Type*) [TensorProductGetY R Y X YX]
    [RCLike R]
    [NormedAddCommGroup Y] [AdjointSpace R Y]
    [NormedAddCommGroup X] [AdjointSpace R X]
    [AddCommGroup YX] [Module R YX]
    [TensorProductType R Y X YX] :
    HMul YX X Y where
  hMul A x := matVecMulAdd (1:R) A x 0 0


/-- Vector matrix multiplication instances.

We use tag class `TensorProductGetX` to infer the product output type `X` and ring `R` -/
instance (R Y X YX : Type*) [TensorProductGetX R Y X YX]
    [RCLike R]
    [NormedAddCommGroup Y] [AdjointSpace R Y]
    [NormedAddCommGroup X] [AdjointSpace R X]
    [AddCommGroup YX] [Module R YX]
    [TensorProductType R Y X YX] :
    HMul Y YX X where
  hMul y A := matHVecMulAdd (1:R) A y 0 0


----------------------------------------------------------------------------------------------------
-- Instances ---------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section Identity
variable {R : Type*} [RCLike R]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X]


-- TODO: !!!Fix this for complex `R`!!! it is missing complex conjugates
open ComplexConjugate
instance : TensorProductType R R X X where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd a x y A := (a*x) • /- star -/ y + A
  matVecMulAdd a A x b y := a*⟪A,x⟫[R] + b*y
  matHVecMulAdd a A y b x := (a*/- conj -/y)•A + b • x
  tmulAdd_eq_tmul := sorry_proof

-- this creates a diamond with the previous for `ttmul` on `R ⊗'[R] R`
-- what to do about this?
-- TODO: !!!Fix this for complex `R`!!! it is missing complex conjugates
instance (priority:=low) : TensorProductType R X R X where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd a x y A := (a*/- conj -/ y)•x + A
  matVecMulAdd a A y b x := (a*y)• /- star -/ A + b • x
  matHVecMulAdd a A x b y := a*⟪A,x⟫[R] + b*y
  tmulAdd_eq_tmul := sorry_proof

instance {R} [RCLike R] : TensorProductGetYX R R X X := ⟨⟩
instance {R} [RCLike R] : TensorProductGetYX R X R X := ⟨⟩

@[simp, simp_core]
theorem tmul_scalar_left (a : R) (x : X) :
  a ⊗[R] x = a • x := by simp[tmul,tmulAdd]

@[simp, simp_core]
theorem tmul_scalar_right (a : R) (x : X) :
  x ⊗[R] a = a • x := by simp[tmul,tmulAdd]

end Identity



section Simps

variable
  {R Y X YX : Type*} [RCLike R]
  [NormedAddCommGroup Y] [AdjointSpace R Y] [NormedAddCommGroup X] [AdjointSpace R X]
  [AddCommGroup YX] [Module R YX]
  [TensorProductType R Y X YX]


section MatVecNotation

variable [TensorProductGetY R Y X YX]

theorem matVecMulAdd_def
    (a b : R) (A : YX) (x : X) (y : Y) :
  matVecMulAdd a A x b y = a•A*x + b•y := sorry_proof

@[simp, simp_core]
theorem matVecMul_zero_A (x : X) : (0 : YX) * x = 0 := sorry_proof

@[simp, simp_core]
theorem matVecMul_zero_x (A : YX) : (A : YX) * (0 : X) = 0 := sorry_proof

theorem add_matVecMul (A B : YX) (x : X) : (A+B)*x = A*x + B*x := sorry_proof
theorem matVecMul_add (A : YX) (x y : X) : A*(x+y) = A*x + A*y := sorry_proof

theorem matVecMul_smul_assoc (a : R) (A : YX) (x : X) : (a•A)*x = a•(A*x) := sorry_proof

end MatVecNotation

section VecMatNotation

variable [TensorProductGetX R Y X YX]

-- TODO: this theorem is missing `(star y)` !!! we would probably add `Star` to `AdjointSpace`
theorem matHVecMulAdd_def
    (a b : R) (A : YX) (x : X) (y : Y) :
  matHVecMulAdd a A y b x = a•/-star-/y*A + b•x := sorry_proof

@[simp, simp_core]
theorem vecMatMul_zero_A (y : Y) : y * (0 : YX) = 0 := sorry_proof

@[simp, simp_core]
theorem vecMatMul_zero_y (A : YX) : (0 : Y) * (A : YX) = 0 := sorry_proof

theorem vecMatMul_add (A B : YX) (y : Y) : y*(A+B) = y*A + y*B := sorry_proof
theorem add_vecMatMul (A : YX) (x y : Y) : (x+y)*A = x*A + y*A := sorry_proof

-- TODO: this is wrong onver complex numbers
--       it is missing some conjugations!!!
theorem vecMatMul_smul_assoc (a : R) (y : Y) (A : YX) : y*(a•A) = a•(y*A) := sorry_proof

end VecMatNotation


@[simp, simp_core]
theorem matVecMulAdd_zero_a (b : R) (A : YX) (x : X) (y : Y) :
    matVecMulAdd 0 A x b y = b•y := by
  have : TensorProductGetY R Y X YX := ⟨⟩
  simp[matVecMulAdd_def]

@[simp, simp_core]
theorem matVecMulAdd_zero_A (a b : R) (x : X) (y : Y) :
    matVecMulAdd a (0 : YX) x b y = b•y := by
  have : TensorProductGetY R Y X YX := ⟨⟩
  simp[matVecMulAdd_def]

@[simp, simp_core]
theorem matVecMulAdd_zero_x (a b : R) (A : YX) (y : Y) :
    matVecMulAdd a A (0:X) b y = b•y := by
  have : TensorProductGetY R Y X YX := ⟨⟩
  simp[matVecMulAdd_def]


@[simp, simp_core]
theorem matHVecMulAdd_zero_a (b : R) (A : YX) (x : X) (y : Y) :
    matHVecMulAdd 0 A y b x = b•x := by
  have : TensorProductGetX R Y X YX := ⟨⟩
  simp[matHVecMulAdd_def]

@[simp, simp_core]
theorem matHVecMulAdd_zero_A (a b : R) (x : X) (y : Y) :
  matHVecMulAdd a (0 : YX) y b x = b•x := by
  have : TensorProductGetX R Y X YX := ⟨⟩
  simp[matHVecMulAdd_def]

@[simp, simp_core]
theorem matHVecMulAdd_zero_y (a b : R) (A : YX) (x : X) :
  matHVecMulAdd a A (0:Y) b x = b•x := by
  have : TensorProductGetX R Y X YX := ⟨⟩
  simp[matHVecMulAdd_def]
