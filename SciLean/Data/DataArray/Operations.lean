import SciLean.Data.DataArray.DataArray
import SciLean.Data.ArrayType.Algebra
import SciLean.Util.Limit

namespace SciLean.DataArrayN

section GeneralFunctions

variable
  {I : Type*} [IndexType I]
  {J : Type*} [IndexType J]
  {K : Type*} [IndexType K]
  {X : Type*} [PlainDataType X]


abbrev mapMono (x : DataArrayN X I) (f : X → X) :=
  ArrayType.mapMono f x

abbrev mapIdxMono (x : DataArrayN X I) (f : I → X → X) :=
  ArrayType.mapIdxMono f x

abbrev foldl (x : DataArrayN X I) (op : X → X → X) (init : X) :=
  IndexType.foldl (fun b i => op b x[i]) init

abbrev reduceD (x : DataArrayN X I) (f : X → X → X) (default : X):=
  IndexType.reduceD (fun i => x[i]) f default

abbrev reduce [Inhabited X] (x : DataArrayN X I) (f : X → X → X) :=
  IndexType.reduce (fun i => x[i]) f


abbrev maxD [Max X] (x : DataArrayN X I) (x₀ : X) : X := x.reduceD (max · ·) x₀
abbrev minD [Min X] (x : DataArrayN X I) (x₀ : X) : X := x.reduceD (min · ·) x₀
abbrev max [Max X] [Inhabited X] (x : DataArrayN X I) : X := x.maxD default
abbrev min [Min X] [Inhabited X] (x : DataArrayN X I) : X := x.minD default


macro "reshape_tactic" : tactic => `(tactic| first | decide | simp | (fail "failed to reshape"))

abbrev reshape1 (x : X^[I]) (n : ℕ)
    (h : Size.size I = n := by reshape_tactic) : X^[n] :=
  x.reshape (Fin n) (by simp[h])


abbrev reshape2 (x : X^[I]) (n₁ n₂ : ℕ)
    (h : Size.size I = n₁*n₂ := by reshape_tactic) : X^[n₁,n₂] :=
  x.reshape (Fin n₁ × Fin n₂) (by simp[h])


abbrev reshape3 (x : X^[I]) (n₁ n₂ n₃ : ℕ)
    (h : Size.size I = n₁*n₂*n₃ := by reshape_tactic) : X^[n₁,n₂,n₃] :=
  x.reshape (Fin n₁ × Fin n₂ × Fin n₃) (by simp[h]; ac_rfl)


abbrev reshape4 (x : X^[I]) (n₁ n₂ n₃ n₄ : ℕ)
    (h : Size.size I = n₁*n₂*n₃*n₄ := by reshape_tactic) : X^[n₁,n₂,n₃,n₄] :=
  x.reshape (Fin n₁ × Fin n₂ × Fin n₃ × Fin n₄) (by simp[h]; ac_rfl)


abbrev reshape5 (x : X^[I]) (n₁ n₂ n₃ n₄ n₅ : ℕ)
    (h : Size.size I = n₁*n₂*n₃*n₄*n₅ := by reshape_tactic) : X^[n₁,n₂,n₃,n₄,n₅] :=
  x.reshape (Fin n₁ × Fin n₂ × Fin n₃ × Fin n₄ × Fin n₅) (by simp[h]; ac_rfl)

end GeneralFunctions

----------------------------------------------------------------------------------------------------
-- Basic Linear Algebra Operations -----------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section LinearAlgebra

variable
  {I : Type} [IndexType I]
  {J : Type} [IndexType J]
  {K : Type} [IndexType K]

variable [DecidableEq I] [DecidableEq J]

variable {R : Type} [inst : RealScalar R] [PlainDataType R]

set_default_scalar R


/-- Identity matrix -/
def identity : R^[I,I] :=
  ⊞ (i j : I) => if i = j then 1 else 0

@[inherit_doc identity]
notation "𝐈" => @identity _ _ _ defaultScalar% _ _

@[inherit_doc identity]
notation "𝐈" n:max => (identity : defaultScalar%^[n,n])

/-- Elemtwise product of two vectors, matrices or tensors -/
def multiply (x y : R^[I]) : R^[I] :=
  x.mapIdxMono (fun i xi => xi * y[i])

/-- Turn vector into diagonal matrix. -/
def diag (x : R^[I]) : R^[I,I] :=
  ⊞ i j => if i = j then x[i] else 0

/-- Extract diagonal from matrix. -/
def diagonal (x : R^[I,I]) : R^[I] :=
  ⊞ i => x[i,i]

/-- Outer product of two vector. -/
def outerprod (x : R^[I]) (y : R^[J]) : R^[I,J] :=
  ⊞ i j => x[i]*y[j]

/-- Sum all elements of a vector, matrix, tensor: `x.sum = ∑ i, x[i]`-/
def sum (x : R^[I]) : R := ∑ i, x[i]

/-- Matrix transpose -/
def transpose (A : R^[I,J]) : R^[J,I] := ⊞ j i => A[i,j]

/-- Make lower triangular matrix out of a vector.

`offset = 1` creates strict lower triangular matrix.

Examples:
```
lowerTriangular ⊞[1,2,3] 2 0
=
⊞[1,0;
  2,3]

lowerTriangular ⊞[1,2,3] 3 1
=
⊞[0,0,0;
  1,0,0;
  2,3,0]

lowerTriangular ⊞[1,2,3] 3 2
=
⊞[0,0,0,0;
  0,0,0,0;
  1,0,0,0;
  2,3,0,0]
```

TODO: allow offset to be integer and output to be rectangular -/
def lowerTriangular {k : ℕ} (x : R^[k]) (n : ℕ) (offset : ℕ := 0)
    (h : k = ((n-offset)*(n+1-offset))/2 := by first | decide | simp_all) : R^[n,n] :=
  ⊞ (i j : Fin n) =>
    if i ≥ j + offset then
      let a := n-offset-j.1
      let b := n-offset
      let colOffset := (((b+a)*(b-a+1))/2) - a
      let idx : Fin k := ⟨i.1-offset-j.1+colOffset, sorry_proof⟩
      x[idx]
    else
      0


/-- Take lower triangular part of a matrix and flatten it to a vector.

To turn the resulting vector into

Examples:
```
lowerTriangularPart ⊞[1,2;
                      3,4] 0
=
⊞[1,3,4]

lowerTriangular ⊞[1,2,3;
                  4,5,6;
                  7,8,9] 0
=
⊞[1,4,7,5,8,9]

lowerTriangular ⊞[1,2,3;
                  4,5,6;
                  7,8,9] 1
=
⊞[4,7,8]
```
-/
def lowerTriangularPart {n : ℕ} (A : R^[n,n]) (offset : ℕ := 0)
    {k} (h : k = ((n-offset)*(n+1-offset))/2 := by simp; infer_var) : R^[k] := Id.run do
  let mut x : R^[k] := 0
  let mut i := offset
  let mut j := 0
  for idx in [0:k] do
    let idx : Fin k := ⟨idx, sorry_proof⟩
    x[idx] := A[⟨i,sorry_proof⟩,⟨j,sorry_proof⟩]
    i := i + 1
    if i ≥ n then
      j := j + 1
      i := offset + j
  return x


@[inherit_doc transpose]
postfix:max "ᵀ" => transpose

/-- Matrix trace: `A.trace = ∑ i, A[i,i]` -/
def trace (A : R^[I,I]) : R := ∑ i, A[i,i]

/-- Dot product between vectors, matrices, tensors: `x.dot y = ∑ i, x[i] * y[i]` -/
def dot (x y : R^[I]) : R := ∑ i, x[i]*y[i]

/-- Matrix × vector multiplication: `A.vecmul x = ⊞ i => ∑ j, A[i,j] * x[j]` -/
def vecmul (A : R^[I,J]) (x : R^[J]) : R^[I] := ⊞ i => ∑ j, A[i,j] * x[j]

instance : HMul (R^[I,J]) (R^[J]) (R^[I]) where
  hMul A x := A.vecmul x

/-- Matrix × matrix multiplication: `A.vecmul B = ⊞ i k => ∑ j, A[i,j] * B[j,k]` -/
def matmul (A : R^[I,J]) (B : R^[J,K]) : R^[I,K] := ⊞ i k => ∑ j, A[i,j] * B[j,k]

instance : HMul (R^[I,J]) (R^[J,K]) (R^[I,K]) where
  hMul A B := A.matmul B

noncomputable
def inv (A : R^[I,I]) : R^[I,I] :=
  (fun B : R^[I,I] => A.matmul B).invFun (𝐈 I)

noncomputable
instance : Inv (R^[I,I]) where
  inv A := A.inv

/-- Invertible matrix proposition -/
def Invertible (A : R^[I,I]) : Prop := (fun B : R^[I,I] => A.matmul B).Bijective

/-- Inverse of transpose matrix `A⁻ᵀ = Aᵀ⁻¹`

Tranpose and inversion commute, i.e. `Aᵀ⁻¹ = A⁻¹ᵀ`, we prefer `Aᵀ⁻¹` and `simp` by default rewrites
`A⁻¹ᵀ` to `Aᵀ⁻¹`. -/
macro:max A:term "⁻ᵀ" :term => `($Aᵀ⁻¹)

@[app_unexpander Inv.inv]
def _root_.Inv.inv.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $A) =>
    match A with
    | `($Aᵀ) => `($A⁻ᵀ)
    | _ => `($A⁻¹)
  | _ => throw ()

/-- Matrix power with natural number exponent -/
def npow (A : R^[I,I]) (n : ℕ) : R^[I,I] :=
  match n with
  | 0 => 𝐈
  | 1 => A
  | n+2 =>
    if n % 2 = 0 then
      npow (A * A) (n/2+1)
    else
      (npow (A * A) (n/2+1)) * A

/-- Derivative of matrix power i.e. `npowDeriv A B n = ∂ (A':=A;B), A^n` -/
def npowDeriv (A B : R^[I,I]) (n : ℕ) : R^[I,I] :=
  match n with
  | 0 => 0
  | 1 => B
  | n+2 =>
    if n % 2 = 0 then
      let A' := npow A (n/2 + 1)
      let B' := npowDeriv A B (n/2 + 1)
      B' * A' + A' * B'
    else
      let A' := npow A (n/2 + 1)
      let B' := npowDeriv A B (n/2 + 1)
      B' * A' * A + A' * B' * A + A' * A' * B

instance : HPow (R^[I,I]) ℕ (R^[I,I]) where
  hPow A n := A.npow n

/-- Matrix power with integer exponent -/
noncomputable
def zpow (A : R^[I,I]) (n : ℤ) : R^[I,I] :=
  if 0 ≤ n then
    A^n.toNat
  else
    A⁻¹ ^ (-n).toNat

noncomputable
instance : HPow (R^[I,I]) ℤ (R^[I,I]) where
  hPow A n := A.zpow n

/-- Matrix determinant -/
noncomputable
def det {R : Type} [RealScalar R] [PlainDataType R] (A : R^[I,I]) : R :=
  let f := LinearMap.mk' R (fun x : R^[I] => (⊞ i => ∑ j, A[i,j] * x[j])) sorry_proof
  LinearMap.det f

/-- Returns solution of `A*x = b` -/
noncomputable
def solve (A : R^[I,I]) (b : R^[I]) := A⁻¹ * b

/-- Returns solution of `A*X = B` -/
noncomputable
def solve' (A : R^[I,I]) (B : R^[I,J]) := A⁻¹ * B

/-- Rank polymorphic solve -/
class Solve (R : Type) (I : Type) (J : Type*)
    [RealScalar R] [PlainDataType R] [IndexType I] [IndexType J] where
  /-- Linear system solve that accepts either vector or matrix as right hand side. -/
  solve (A : R^[I,I]) (b : R^[J]) : R^[J]

noncomputable
instance : Solve R I I where
  solve A b := A.solve b

noncomputable
instance : Solve R I (I×J) where
  solve A B := A.solve' B

/-- Cross product of two vector. -/
def cross (x y : R^[3]) : R^[3] :=
  ⊞[x[1]*y[2] - x[2]*y[1],
    x[2]*y[0] - x[0]*y[2],
    x[0]*y[1] - x[1]*y[0]]

/-- Matrix corresponding to taking cross product with `x`  -/
def crossmatrix (x : R^[3]) : R^[3,3] := Id.run do
  let mut A : R^[3,3] := 0
  A[0,2] := x[1]; A[0,1] := - x[2]
  A[1,0] := x[2]; A[1,2] := - x[0]
  A[2,1] := x[0]; A[2,0] := - x[1]
  return A

/-- Takes antisymmetric part of matrix `A` and stacks into a vector. -/
def antisymmpart (A : R^[3,3]) : R^[3] :=
  ⊞[0.5 * (A[2,1] - A[1,2]), 0.5 * (A[0,2] - A[2,0]), 0.5 * (A[1,0] - A[0,1])]

/-- Cayley Map: https://en.wikipedia.org/wiki/Cayley_transform#Matrix_map -/
noncomputable
def caley (A : R^[I,I]) := (𝐈 + A).solve' (𝐈 - A)

/-- Matrix exponential -/
noncomputable
def matexp (A : R^[I,I]) := limit n → ∞, ∑ (i : Fin n), (i.1.factorial : R)⁻¹ • A^i.1

/-- Take function between two vector spaces and return corresponding matrix. -/
@[fun_trans]
def toMatrix [Basis J R X] [Basis I R Y] [Inner R Y] (f : X → Y) : R^[I,J] :=
  ⊞ (i : I) (j : J) => ⟪ⅇ i, (f (ⅇ j))⟫


----------------------------------------------------------------------------------------------------
-- Commong Nonlinear Operations --------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

set_default_scalar R

open Scalar

/-- Softmax turns array into an array of values in (0,1) -/
def softmax (x : R^[I]) : R^[I] :=
  let xmax := x.max
  let w := ∑ i, exp (x[i] - xmax)
  ⊞ i => exp (x[i] - xmax) / w

/-- Logarithm of sum of exponentials, its derivative is softmax.

Common when doing maximul likelihood. -/
def logsumexp (x : R^[I]) : R :=
  let xmax := x.max
  log (∑ i, exp (x[i] - xmax)) + xmax

/-- Elementwise exponential -/
def exp (x : R^[I]) : R^[I] :=
  x.mapMono (fun xi => Scalar.exp xi)

/-- Elementwise logarithm -/
def log (x : R^[I]) : R^[I] :=
  x.mapMono (fun xi => Scalar.log xi)
