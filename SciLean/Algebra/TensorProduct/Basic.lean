
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Erased

import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.AdjointSpace.CanonicalBasis
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


----------------------------------------------------------------------------------------------------
-- TMul --------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


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

open scoped RightActions

open ComplexConjugate MulOpposite
instance tpScalarLeft [SMul (Rᵐᵒᵖ) X] [Star X] :
    TensorProductType R R X X where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd a x y A := a•(x•y) + A
  matVecMulAdd a A x b y := a*⟪A,x⟫[R] + b*y
  vecMatMulAdd a y A b x := a•(A <• (conj y)) + b • x
  tmulAdd_eq_tmul := sorry_proof


/-
Note: `op y • x` is the way todo right scalar multiplication of `x : X` by `y : R`.
-/
open MulOpposite in
instance (priority:=low) tpScalarRight
  [SMul (Rᵐᵒᵖ) X] [Star X] :
  TensorProductType R X R X where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd a x y A := a•(x <• y) + A
  matVecMulAdd a A y b x := a•(y • star A) + b • x
  vecMatMulAdd a x A b y := a*⟪x, A⟫[R] + b*y
  tmulAdd_eq_tmul := sorry_proof

instance {R} [RCLike R] : TensorProductGetYX R R X X := ⟨⟩
instance {R} [RCLike R] : TensorProductGetYX R X R X := ⟨⟩

attribute [ext] TensorProductType

-- This is crucual defeq that prevents potential TC diamond!
example : (tpScalarLeft : TensorProductType R R R R)
          =
          (tpScalarRight : TensorProductType R R R R) := by rfl



@[simp, simp_core]
theorem tmul_scalar_left [SMul (Rᵐᵒᵖ) X] [Star X] (a : R) (x : X) :
  a ⊗[R] x = a • x := by simp[tmul,tmulAdd]

open MulOpposite in
@[simp, simp_core]
theorem tmul_scalar_right [SMul (Rᵐᵒᵖ) X] [Star X] (a : R) (x : X) :
  x ⊗[R] a = (op a) • x := by simp[tmul,tmulAdd]

end Identity


----------------------------------------------------------------------------------------------------
-- Simps and theorems ------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section Simps

variable
  {R Y X YX : Type*} [RCLike R]
  [NormedAddCommGroup Y] [AdjointSpace R Y] [NormedAddCommGroup X] [AdjointSpace R X]
  [NormedAddCommGroup YX] [AdjointSpace R YX]
  [TensorProductType R Y X YX]


-- basic properties of `tmul`

@[simp, simp_core]
theorem tmul_zero (y : Y) : y ⊗[R] (0 : X) = 0 := by sorry_proof

@[simp, simp_core]
theorem zero_tmul (x : X) : (0 : Y) ⊗[R] x = 0 := by sorry_proof

@[fun_prop]
theorem tmul.arg_xy.Continuous_rule :
  Continuous (fun yx : Y×X => yx.1⊗[R]yx.2) := sorry_proof

@[fun_prop]
theorem tmul.arg_x.IsContinuousLinearMap_rule (y : Y) :
  IsContinuousLinearMap R (fun x : X => y⊗[R]x) := sorry_proof

@[fun_prop]
theorem tmul.arg_y.IsContinuousLinearMap_rule (x : X) :
  IsContinuousLinearMap R (fun y : Y => y⊗[R]x) := sorry_proof


-- basic properties of `matVecMulAdd`

@[simp, simp_core]
theorem matVecMulAdd_zero_a (b : R) (A : YX) (x : X) (y : Y) :
    matVecMulAdd 0 A x b y = b•y := by sorry_proof

@[simp, simp_core]
theorem matVecMulAdd_zero_A (a b : R) (x : X) (y : Y) :
    matVecMulAdd a (0 : YX) x b y = b•y := by sorry_proof

@[simp, simp_core]
theorem matVecMulAdd_zero_x (a b : R) (A : YX) (y : Y) :
    matVecMulAdd a A (0:X) b y = b•y := by sorry_proof


-- basic properties of `vecMatMulAdd`

@[simp, simp_core]
theorem vecMatMulAdd_zero_a (b : R) (A : YX) (x : X) (y : Y) :
    vecMatMulAdd 0 y A b x = b•x := by sorry_proof

@[simp, simp_core]
theorem vecMatMulAdd_zero_A (a b : R) (x : X) (y : Y) :
  vecMatMulAdd a y (0 : YX) b x = b•x := by sorry_proof

@[simp, simp_core]
theorem vecMatMulAdd_zero_y (a b : R) (A : YX) (x : X) :
  vecMatMulAdd a (0:Y) A b x = b•x := by sorry_proof


----------------------------------------------------------------------------------------------------
-- Operations --------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------



variable
    {𝕜 X Y Z W : Type*}
    [RCLike 𝕜]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
    [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
    [NormedAddCommGroup W] [AdjointSpace 𝕜 W]
    {XY : Type*} [NormedAddCommGroup XY] [AdjointSpace 𝕜 XY] [TensorProductType 𝕜 X Y XY]
    {YX : Type*} [NormedAddCommGroup YX] [AdjointSpace 𝕜 YX] [TensorProductType 𝕜 Y X YX]
    {ZW : Type*} [NormedAddCommGroup ZW] [AdjointSpace 𝕜 ZW] [TensorProductType 𝕜 Z W ZW]
    {I} [Fintype I] [CanonicalBasis I 𝕜 X]
    {J} [Fintype J] [CanonicalBasis J 𝕜 Y]

set_default_scalar 𝕜

def tcurry (f : X ⊗ Y → Z) (x : X) (y : Y) : Z := f (x⊗y)

open Classical in
/--
Uncurry bilinear map `f : X → Y → Z` to a linear map over tensor product `X ⊗ Y`
-/
noncomputable
def tuncurry (f : X →L[𝕜] Y →L[𝕜] Z) (xy : X⊗Y) : Z :=
  if h : ∃ (g : X⊗Y → Z), ∀ x y, tcurry (𝕜:=𝕜) g x y = f x y then
    choose h xy
  else
    0


open Classical in

/--
Combine two linear maps to a single linear map over the tensor product of its domains and codomains.
-/
noncomputable
def tmap (f : X →L[𝕜] Z) (g : Y →L[𝕜] W) (xy : X⊗Y) : Z⊗W :=
  if h : ∃ (F : X⊗Y →L[𝕜] Z⊗W), ∀ (x:X) (y:Y), F (x⊗y) = f x ⊗ g y then
    choose h xy
  else
    0

@[fun_prop]
theorem tmap.arg_xy.IsContinuousLinearMap_rule (f : X →L[𝕜] Z) (g : Y →L[𝕜] W) :
    IsContinuousLinearMap 𝕜 (fun xy => tmap f g xy) := by unfold tmap; fun_prop

open Classical in
noncomputable
def tswap [TensorProductGetRXY 𝕜 X Y XY] (xy : X⊗Y) : Y⊗X :=
  if h : ∃ (F : X⊗Y →L[𝕜] Y⊗X), ∀ (x:X) (y:Y), F (x⊗y) = y⊗x then
    choose h xy
  else
    0

@[fun_prop]
theorem tswap.arg_xy.IsContinuousLinearMap_rule [TensorProductGetRXY 𝕜 X Y XY] :
    IsContinuousLinearMap 𝕜 (fun xy : X⊗Y => tswap xy) := by unfold tswap; fun_prop



variable
  {YZ : Type*} [NormedAddCommGroup YZ] [AdjointSpace 𝕜 YZ] [TensorProductType 𝕜 Y Z YZ]
  {X_YZ : Type*} [NormedAddCommGroup X_YZ] [AdjointSpace 𝕜 X_YZ] [TensorProductType 𝕜 X YZ X_YZ]
  {XY_Z : Type*} [NormedAddCommGroup XY_Z] [AdjointSpace 𝕜 XY_Z] [TensorProductType 𝕜 XY Z XY_Z]

open Classical in
/--
Associate tensor product to the left.
-/
noncomputable
def tassocl [TensorProductGetRXY 𝕜 X YZ X_YZ] [TensorProductGetRXY 𝕜 Y Z YZ] (x_yz : X⊗(Y⊗Z)) : (X⊗Y)⊗Z :=
  if h : ∃ (F : X⊗(Y⊗Z) →L[𝕜] (X⊗Y)⊗Z), ∀ (x:X) (y:Y) (z:Z), F (x⊗(y⊗z)) = (x⊗y)⊗z then
    choose h x_yz
  else
    0

open Classical in
/--
Associate tensor product to the right.
-/
noncomputable
def tassocr [TensorProductGetRXY 𝕜 XY Z XY_Z] [TensorProductGetRXY 𝕜 X Y XY] (xy_z : (X⊗Y)⊗Z) : X⊗(Y⊗Z) :=
  if h : ∃ (F : (X⊗Y)⊗Z →L[𝕜] X⊗(Y⊗Z)), ∀ (x:X) (y:Y) (z:Z), F ((x⊗y)⊗z) = x⊗(y⊗z) then
    choose h xy_z
  else
    0


@[fun_prop]
theorem tassocl.arg_x_yz.IsContinuousLinearMap_rule [TensorProductGetRXY 𝕜 X YZ X_YZ] [TensorProductGetRXY 𝕜 Y Z YZ] :
    IsContinuousLinearMap 𝕜 (fun x_yz : X⊗(Y⊗Z) => tassocl x_yz) := by unfold tassocl; fun_prop

@[fun_prop]
theorem tassocr.arg_xy_z.IsContinuousLinearMap_rule [TensorProductGetRXY 𝕜 XY Z XY_Z] [TensorProductGetRXY 𝕜 X Y XY] :
    IsContinuousLinearMap 𝕜 (fun xy_z : (X⊗Y)⊗Z => tassocr xy_z) := by unfold tassocr; fun_prop
