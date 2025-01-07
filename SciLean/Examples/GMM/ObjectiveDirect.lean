import SciLean
import SciLean.Analysis.SpecialFunctions.MultiGamma

open SciLean


variable {M V R} [RealScalar R] [VectorType V R] [MatrixType M V]
  [∀ n [IndexType n], PlainDataType (V n)]
  [∀ n m [IndexType n] [IndexType m], PlainDataType (M n m)]

set_default_scalar R

-- local macro (priority:=high+1) "Float^[" M:term ", " N:term "]" : term =>
--   `(FloatMatrix' .RowMajor .normal (Fin $M) (Fin $N))

-- local macro (priority:=high+1) "Float^[" N:term "]" : term =>
--   `(FloatVector (Fin $N))

-- -- notation: `v[i] := vᵢ`
-- local macro (priority:=high+10) id:ident noWs "[" i:term "]" " := " v:term : doElem =>
--    `(doElem| $id:ident := VectorType.set $id $i $v)

-- -- notation: `A[i,:] := r`
-- local macro (priority:=high+10) id:ident noWs "[" i:term "," ":" "]" " := " v:term : doElem =>
--    `(doElem| $id:ident := MatrixType.updateRow $id $i $v)

-- -- notation: `⊞ i => vᵢ`
-- open Lean Parser Term in
-- local macro (priority:=high+10) "⊞" i:funBinder " => " b:term : term =>
--    `(term| VectorType.fromVec  fun $i => $b)



open DenseMatrixType VectorType Scalar in
/-- unlack `logdiag` and `lt` to lower triangular matrix -/
def unpackQ {d : Nat} (logdiag : V (Fin d)) (lt : V (Fin ((d-1)*d/2))) : M (Fin d) (Fin d)  :=
  MatrixType.fromMatrix fun i j =>
    if i < j then 0
       else if i == j then exp (toVec logdiag i)
       else
         let idx : Fin ((d-1)*d/2) := ⟨d*j.1 + i.1 - j.1 - 1 - (j.1 * (j.1+1))/2, sorry_proof⟩
         (toVec lt idx)


open Scalar in
def logWishartPrior {k d : Nat} (Qs : (M (Fin d) (Fin d))^[k]) (qsums : V (Fin k)) (wishartGamma : R) (wishartM : Nat) :=
    let p := d
    let n := p + wishartM + 1
    let c := (n * p) * (log wishartGamma - 0.5 * log 2) - (logMultiGamma ((0.5:R) * n) p)
    let frobenius : R := ∑ i, ‖Qs[i]‖₂²
    let sumQs := VectorType.sum qsums
    0.5 * wishartGamma * wishartGamma * frobenius - wishartM * sumQs - k * c


open Scalar VectorType in
def gmmObjective {d k n : Nat}
      (alphas: V (Fin k)) (means: M (Fin k) (Fin d))
      (logdiag : M (Fin k) (Fin d)) (lt : M (Fin k) (Fin ((d-1)*d/2)))
      (x : M (Fin n) (Fin d)) (wishartGamma : R) (wishartM: Nat) :=
    let C := -(n * d * 0.5 * log (2 * π))

    -- qsAndSums
    let Qs := ⊞ i => unpackQ (M:=M) (MatrixType.row logdiag i) (MatrixType.row lt i)
    let qsums : V (Fin k) := VectorType.fromVec (fun i => VectorType.sum (MatrixType.row logdiag i))

    let slse :=
      ∑ (i : Fin n), logsumexp (VectorType.fromVec (X:=V (Fin k))
        fun (j : Fin k) =>
          toVec alphas j
          +
          toVec qsums j
          -
          0.5 * ‖MatrixType.gemv 1 1 Qs[j] ((MatrixType.row x i) - (MatrixType.row means j)) 0‖₂²)

    C + slse  - n * logsumexp alphas + logWishartPrior Qs qsums wishartGamma wishartM


-- def objective (data : GMMDataRaw) : Float :=
--   let ⟨d,k,n,data⟩ := data.toGMMData
--   gmmObjective data.alpha data.means data.logdiag data.lt data.x data.gamma data.m


-- #eval show IO Unit from do

--   for idx in fullRange (Fin 3 × Fin 3) do
--     IO.println idx
