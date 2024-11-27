import SciLean.Data.DataArray.DataArray
import SciLean.Data.ArrayType.Algebra
import SciLean.Util.Limit

namespace SciLean.DataArrayN

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


----------------------------------------------------------------------------------------------------
-- Basic Linear Algebra Operations -----------------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable [DecidableEq I] [DecidableEq J]

variable {R : Type*} [inst : RealScalar R] [PlainDataType R]
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
def det {R} [RealScalar R] [PlainDataType R] (A : R^[I,I]) : R :=
  let f := LinearMap.mk' R (fun x : R^[I] => (⊞ i => ∑ j, A[i,j] * x[j])) sorry_proof
  LinearMap.det f

/-- Returns solution of `A*x = b` -/
noncomputable
def solve (A : R^[I,I]) (b : R^[I]) := A⁻¹ * b

/-- Returns solution of `A*X = B` -/
noncomputable
def solve' (A : R^[I,I]) (B : R^[I,J]) := A⁻¹ * B

/-- Rank polymorphic solve -/
class Solve (R : Type*) (I : Type*) (J : Type*)
    [RealScalar R] [PlainDataType R] [IndexType I] [IndexType J] where
  /-- Linear system solve that accepts either vector or matrix as right hand side. -/
  solve (A : R^[I,I]) (b : R^[J]) : R^[J]

noncomputable
instance : Solve R I I where
  solve A b := A.solve b

noncomputable
instance : Solve R I (I×J) where
  solve A B := A.solve' B


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
