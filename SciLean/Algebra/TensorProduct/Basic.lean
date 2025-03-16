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
def AdjointSpace.toDual (𝕜 : Type u_1) {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E] [AdjointSpace 𝕜 E] (x : E) : Dual 𝕜 E := fun x' =>L[𝕜] ⟪x,x'⟫[𝕜]


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
    tmulAdd : R → Y → X → YX → YX

    /-- Matrix vector multiplication
    ```
    matVecMul a A x b y = a•A*x + b•y
    ```
    -/
    matVecMul : R → YX → X → R → Y → Y

    /-- Conjugate/transpose matrix vector multiplication
    ```
    vecMul a A y b x = a•Aᴴ*y + b•x
    ```
    -/
    matHVecMul : R → YX → Y → R → X → X

    tmulAdd_eq_tmul : ∀ r x y A,
      equiv.out (tmulAdd r y x A)
      =
      r • (y ⊗ₜ[R] toDual R x) + equiv.out A


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
  hMul A x := matVecMul (1:R) A x 0 0


----------------------------------------------------------------------------------------------------
-- Instances ---------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section Identity
variable {R : Type*} [RCLike R]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X]


-- TODO: !!!Fix this for complex `R`!!! it is missing complex conjugates
open ComplexConjugate
set_option trace.Meta.Tactic.simp.discharge true in
instance : TensorProductType R R X X where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd a x y A := (a*x) • /- star -/ y + A
  matVecMul a A x b y := a*⟪A,x⟫[R] + b*y
  matHVecMul a A y b x := (a*/- conj -/y)•A + b • x
  tmulAdd_eq_tmul := sorry_proof

-- this creates a diamond with the previous for `ttmul` on `R ⊗'[R] R`
-- what to do about this?
-- TODO: !!!Fix this for complex `R`!!! it is missing complex conjugates
instance (priority:=low) : TensorProductType R X R X where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd a x y A := (a*/- conj -/ y)•x + A
  matVecMul a A y b x := (a*y)• /- star -/ A + b • x
  matHVecMul a A x b y := a*⟪A,x⟫[R] + b*y
  tmulAdd_eq_tmul := sorry_proof

instance {R} [RCLike R] : TensorProductGetYX R R X X := ⟨⟩
instance {R} [RCLike R] : TensorProductGetYX R X R X := ⟨⟩

end Identity
