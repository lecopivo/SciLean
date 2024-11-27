import SciLean.Data.DataArray.DataArray
import SciLean.Data.ArrayType.Algebra

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


variable [DecidableEq I]

variable {R : Type*} [inst : RealScalar R] [PlainDataType R]
  -- [Add X] [Sub X] [Mul X] [Zero X] [One X]

def _root_.SciLean.Matrix.identity : R^[I,I] :=
  ⊞ (i j : I) => if i = j then 1 else 0

def multiply (x y : R^[I]) : R^[I] :=
  x.mapIdxMono (fun i xi => xi * y[i])

def diag (x : R^[I]) : R^[I,I] :=
  ⊞ i j => if i = j then x[i] else 0

def diagonal (x : R^[I,I]) : R^[I] :=
  ⊞ i => x[i,i]

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

/-- Matrix × matrix multiplication: `A.vecmul B = ⊞ i k => ∑ j, A[i,j] * B[j,k]` -/
def matmul (A : R^[I,J]) (B : R^[J,K]) : R^[I,K] := ⊞ i k => ∑ j, A[i,j] * B[j,k]


noncomputable
def inv (A : R^[I,I]) : R^[I,I] :=
  (fun B : R^[I,I] => A.matmul B).invFun Matrix.identity

/-- Invertible matrix proposition -/
def Invertible (A : R^[I,I]) : Prop := (fun B : R^[I,I] => A.matmul B).Bijective

def npow (A : R^[I,I]) (n : ℕ) : R^[I,I] :=
  match n with
  | 0 => Matrix.identity
  | 1 => A
  | n+2 =>
    if n % 2 = 0 then
      npow (A.matmul A) (n/2+1)
    else
      (npow (A.matmul A) (n/2+1)).matmul A


noncomputable
def zpow (A : R^[I,I]) (n : ℤ) : R^[I,I] :=
  if 0 ≤ n then
    A.npow n.toNat
  else
    A.inv.npow (-n).toNat

/-- Matrix determinant -/
noncomputable
def det {R} [RealScalar R] [PlainDataType R] (A : R^[I,I]) : R :=
  let f := LinearMap.mk' R (fun x : R^[I] => (⊞ i => ∑ j, A[i,j] * x[j])) sorry_proof
  LinearMap.det f


namespace Matrix

instance : HMul (R^[I,J]) (R^[J,K]) (R^[I,K]) where
  hMul A B := A.matmul B

instance : HMul (R^[I,J]) (R^[J]) (R^[I]) where
  hMul A x := A.vecmul x

instance : HPow (R^[I,I]) ℕ (R^[I,I]) where
  hPow A n := A.npow n

noncomputable
instance : Inv (R^[I,I]) where
  inv A := A.inv

noncomputable
instance : HPow (R^[I,I]) ℤ (R^[I,I]) where
  hPow A n := A.zpow n

end Matrix

noncomputable
def solve (A : R^[I,I]) (b : R^[I]) := A⁻¹ * b

noncomputable
def solve' (A : R^[I,I]) (B : R^[I,J]) := A⁻¹ * B


set_default_scalar R

open Scalar

def softmax (x : R^[I]) : R^[I] :=
  let xmax := x.maxD 0
  let w := ∑ i, exp (x[i] - xmax)
  ⊞ i => exp (x[i] - xmax) / w

def softmax' (x dx : R^[I]) : R :=
  let xmax := x.maxD 0
  let w := ∑ i, exp (x[i] - xmax)
  let z := ∑ i, dx[i] * exp (x[i] - xmax)
  z / w

def logsumexp (x : R^[I]) : R :=
  let xmax := IndexType.maxD (x[·]) 0
  log (∑ i, exp (x[i] - xmax)) - xmax

/-- Elementwise exponential -/
def exp (x : R^[I]) : R^[I] :=
  x.mapMono (fun xi => Scalar.exp xi)

/-- Elementwise logarithm -/
def log (x : R^[I]) : R^[I] :=
  x.mapMono (fun xi => Scalar.log xi)
