import SciLean
import SciLean.Analysis.SpecialFunctions.MultiGamma

open SciLean

set_default_scalar Float

local macro (priority:=high+1) "Float^[" M:term ", " N:term "]" : term =>
  `(FloatMatrix' .RowMajor .normal (Fin $M) (Fin $N))

local macro (priority:=high+1) "Float^[" N:term "]" : term =>
  `(FloatVector (Fin $N))

-- -- notation: `v[i] := vᵢ`
-- local macro (priority:=high+10) id:ident noWs "[" i:term "]" " := " v:term : doElem =>
--    `(doElem| $id:ident := VectorType.set $id $i $v)

-- notation: `A[i,:] := r`
local macro (priority:=high+10) id:ident noWs "[" i:term "," ":" "]" " := " v:term : doElem =>
   `(doElem| $id:ident := MatrixType.updateRow $id $i $v)

-- -- notation: `⊞ i => vᵢ`
-- open Lean Parser Term in
-- local macro (priority:=high+10) "⊞" i:funBinder " => " b:term : term =>
--    `(term| VectorType.fromVec  fun $i => $b)

open DenseMatrixType VectorType Scalar in
/-- unlack `logdiag` and `lt` to lower triangular matrix -/
def unpackQ {d : Nat} (logdiag : Float^[d]) (lt : Float^[(d-1)*d/2]) : Float^[d,d] :=
  MatrixType.fromMatrix fun i j =>
    if i < j then 0
       else if i == j then exp (toVec logdiag i)
       else
         let idx : Fin ((d-1)*d/2) := ⟨d*j.1 + i.1 - j.1 - 1 - (j.1 * (j.1+1))/2, sorry_proof⟩
         (toVec lt idx)


open Scalar in
def logWishartPrior {k d : Nat} (Qs : (Float^[d,d])^[k]) (qsums : Float^[k]) (wishartGamma : Float) (wishartM : Nat) :=
    let p := d
    let n := p + wishartM + 1
    let c := (n * p) * (log wishartGamma - 0.5 * log 2) - (logMultiGamma ((0.5:Float) * n) p)
    let frobenius := ‖Qs‖₂²[Float]
    let sumQs := VectorType.sum qsums
    0.5 * wishartGamma * wishartGamma * frobenius - wishartM * sumQs - k * c


open Scalar VectorType in
def gmmObjective {d k n : Nat}
      (alphas: Float^[k]) (means: Float^[k,d])
      (logdiag : Float^[k,d]) (lt : Float^[k,(d-1)*d/2])
      (x : Float^[n,d]) (wishartGamma : Float) (wishartM: Nat) :=
    let C := -(n * d * 0.5 * log (2 * π))

    -- qsAndSums
    let Qs := ⊞ i => unpackQ (MatrixType.row logdiag i) (MatrixType.row lt i)
    let qsums := VectorType.fromVec (X:=Float^[k]) (fun i => VectorType.sum (MatrixType.row logdiag i))

    let slse :=
      ∑ (i : Fin n), logsumexp (VectorType.fromVec (X:=Float^[k])
        fun (j : Fin k) =>
          toVec alphas j
          +
          toVec qsums j
          -
          0.5 * ‖MatrixType.gemv 1 1 Qs[j] ((MatrixType.row x i) - (MatrixType.row means j)) 0‖₂²[Float])

    C + slse  - n * logsumexp alphas + logWishartPrior Qs qsums wishartGamma wishartM


-- def objective (data : GMMDataRaw) : Float :=
--   let ⟨d,k,n,data⟩ := data.toGMMData
--   gmmObjective data.alpha data.means data.logdiag data.lt data.x data.gamma data.m


-- #eval show IO Unit from do

--   for idx in fullRange (Fin 3 × Fin 3) do
--     IO.println idx
