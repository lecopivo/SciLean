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
  [Add X] [Sub X] [Mul X] [Zero X] [One X]

def _root_.SciLean.Matrix.identity : X^[I,I] :=
  ⊞ (i j : I) => if i = j then 1 else 0

def multiply (x y : X^[I]) : X^[I] :=
  x.mapIdxMono (fun i xi => xi * y[i])

def diag (x : X^[I]) : X^[I,I] :=
  ⊞ i j => if i = j then x[i] else 0

def kronprod (x : X^[I]) (y : X^[J]) : X^[I,J] :=
  ⊞ i j => x[i]*y[j]

-- todo: maybe add complex conjugate
def dot (x y : X^[I]) : X := ∑ i, x[i]*y[i]

def vecmul (A : X^[I,J]) (x : X^[J]) : X^[I] := ⊞ i => ∑ j, A[i,j] * x[j]

def matmul (A : X^[I,J]) (B : X^[J,K]) : X^[I,K] := ⊞ i k => ∑ j, A[i,j] * B[j,k]

noncomputable
def inv (A : X^[I,I]) : X^[I,I] :=
  (fun B : X^[I,I] => A.matmul B).invFun Matrix.identity

def npow (A : X^[I,I]) (n : ℕ) : X^[I,I] :=
  if h : n = 0 then
    Matrix.identity
  else if _ : n = 1 then
    A
  else
    have : n.log2 < n := by apply (Nat.log2_lt h).2; exact Nat.lt_two_pow n
    if n % 2 = 0 then
      npow (A.matmul A) (n/2)
    else
      (npow (A.matmul A) (n/2)).matmul A

noncomputable
def zpow (A : X^[I,I]) (n : ℤ) : X^[I,I] :=
  if 0 ≤ n then
    A.npow n.toNat
  else
    A.inv.npow (-n).toNat


namespace Matrix

variable [Add X] [Mul X] [Sub X] [Zero X] [One X]

instance : HMul (X^[I,J]) (X^[J,K]) (X^[I,K]) where
  hMul A B := A.matmul B

instance : HMul (X^[I,J]) (X^[J]) (X^[I]) where
  hMul A x := A.vecmul x

instance : HPow (X^[I,I]) ℕ (X^[I,I]) where
  hPow A n := A.npow n

noncomputable
instance : Inv (X^[I,I]) where
  inv A := A.inv

noncomputable
instance : HPow (X^[I,I]) ℤ (X^[I,I]) where
  hPow A n := A.zpow n

end Matrix

variable {R : Type*} [RealScalar R] [PlainDataType R] [DecidableEq I]
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
