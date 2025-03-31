import SciLean

open SciLean Scalar

set_option pp.deepTerms true
set_option pp.proofs false

set_default_scalar Float

@[data_synth]
theorem sadf
 {R} [RCLike R]
 {X} [NormedAddCommGroup X] [AdjointSpace R X]
 {I J nI nJ} [IndexType I nI] [IndexType J nJ] [Fold I] [Fold J] :
 HasRevFDeriv R (fun f : I → J → X => ↿f) (fun f => (↿f, fun df i j => df (i,j))) := sorry_proof


/-- unlack `logdiag` and `lt` to lower triangular matrix -/
def unpackQ {d : Nat} (logdiag : Float^[d]) (lt : Float^[((d-1)*d/2)]) : Float^[d,d]  :=
  ⊞ (i : Idx d) (j : Idx d) =>
    if h : i < j then 0
       else if h' : i == j then exp (logdiag[i])
       else
         let idx : Idx ((d-1)*d/2) := ⟨d.toUSize*j.1 + i.1 - j.1 - 1 - (j.1 * (j.1+1))/2,
                                       have := h; have := h'; sorry_proof⟩
         (lt[idx])

abbrev_data_synth unpackQ in logdiag lt : HasRevFDeriv Float by
  unfold unpackQ; dsimp
  data_synth => enter[3]; lsimp [↓let_ite_normalize]

def logWishartPrior {k d : Nat} (Qs : Float^[d,d]^[k]) (qsums : Float^[k]) (wishartGamma : Float) (wishartM : Nat) :=
    let p := d
    let n := p + wishartM + 1
    let c := (n * p) * (log wishartGamma - 0.5 * log 2) - (logMultiGamma (0.5 * n.toFloat) p)
    let frobenius : Float := ‖Qs‖₂²
    let sumQs : Float := qsums.sum
    0.5 * wishartGamma * wishartGamma * frobenius - wishartM * sumQs - k * c


abbrev_data_synth logWishartPrior in Qs qsums : HasRevFDeriv Float by
  unfold logWishartPrior;
  data_synth => enter[3]; lsimp



def gmmObjective {d k n : Nat}
      (alphas: Float^[k]) (means: Float^[k,d])
      (logdiag : Float^[k,d]) (lt : Float^[k,((d-1)*d)/2])
      (x : Float^[n,d]) (wishartGamma : Float) (wishartM: Nat) :=
    let C := -(n * d * 0.5 * log (2 * π))

    -- qsAndSums
    let Qs := ⊞ i => unpackQ (logdiag.row i) (lt.row i)
    let qsums := logdiag.sumRows

    let slse : Float :=
      ∑ᴵ (i : Idx n),  (⊞ (j : Idx k) =>
          alphas[j]
          +
          qsums[j]
          -
          0.5 * ‖Qs[j] * ((x.row i) - (means.row j))‖₂²).logsumexp

    C + slse - n * alphas.logsumexp + logWishartPrior Qs qsums wishartGamma wishartM


def gmmObjective' {d k n : Nat}
      (alphas: Float^[k]) (means: Float^[k,d])
      (logdiag : Float^[k,d]) (lt : Float^[k,((d-1)*d)/2])
      (x : Float^[n,d]) (wishartGamma : Float) (wishartM: Nat) :=
    let C := -(n * d * 0.5 * log (2 * π))

    -- qsAndSums
    let Qs := ⊞ i => unpackQ (logdiag.row i) (lt.row i)
    let qsums := logdiag.sumRows

    let slse : Float :=
      ∑ᴵ (i : Idx n),  (⊞ (j : Idx k) =>
          alphas[j]
          +
          qsums[j]
          -
          let zero : Float^[d] := 0
          let dx := (x.row i) - (means.row j)
          0.5 * ‖(⟨BLAS.LevelTwoData.gemv .RowMajor .NoTrans d d (1:Float) ⟨Qs.1.1,sorry_proof⟩ (j.1*d.toUSize*d.toUSize).toNat d dx.1 0 1 (0:Float) zero.1 0 1,sorry_proof⟩ : Float^[d])‖₂²).logsumexp

    C + slse - n * alphas.logsumexp + logWishartPrior Qs qsums wishartGamma wishartM



abbrev_data_synth gmmObjective in alphas means logdiag lt : HasRevFDeriv Float by
  unfold gmmObjective
  data_synth => enter[3]; lsimp


#check Nat


#check uniformI

def gradient {d k n : Nat}
      (alphas: Float^[k]) (means: Float^[k,d])
      (logdiag : Float^[k,d]) (lt : Float^[k,((d-1)*d)/2])
      (x : Float^[n,d]) (wishartGamma : Float) (wishartM: Nat) :=
  ((<∂ x':=(alphas,means,logdiag,lt), gmmObjective x'.1 x'.2.1 x'.2.2.1 x'.2.2.2 x 1.0 1).2 1)
  rewrite_by
    autodiff


#check Nat

def _root_.SciLean.DataArrayN.rand {X I nI} [IndexType I nI] [FoldM I SciLean.Rand] [PlainDataType X]
    (r : SciLean.Rand X) : SciLean.Rand (X^[I]) := do
  let mut data : DataArray X := .mkEmpty nI
  for _ in [:I] do
    data := data.push (← r)
  return ⟨data, sorry_proof⟩

def main : IO Unit := do

  let d := 64
  let n := 1000
  let k := 100

      -- (alphas: Float^[k]) (means: Float^[k,d])
      -- (logdiag : Float^[k,d]) (lt : Float^[k,((d-1)*d)/2])
      -- (x : Float^[n,d]) (wishartGamma : Float) (wishartM: Nat)
  IO.setRandSeed 0
  let alphas : Float^[k] ← (DataArrayN.rand (uniformI Float)).get
  let means : Float^[k,d] ← (DataArrayN.rand (uniformI Float)).get
  let logdiag : Float^[k,d] ← (DataArrayN.rand (uniformI Float)).get
  let lt : Float^[k,((d-1)*d)/2] ← (DataArrayN.rand (uniformI Float)).get
  let x : Float^[n,d] ← (DataArrayN.rand (uniformI Float)).get

  IO.println
    s!"GMM profile test\n\
       k := {k}, n := {n}, d := {d}"
  IO.println ""


  let s ← IO.monoNanosNow
  let loss := gmmObjective alphas means logdiag lt x 1.0 1
  let e ← IO.monoNanosNow
  let timeNs := e - s
  let timeMs := timeNs.toFloat / 1e6
  IO.println
    s!"GMM                    time := {timeMs}ms \tloss := {loss}"

  IO.sleep 1000

  let s ← IO.monoNanosNow
  let loss := gmmObjective' alphas means logdiag lt x 1.0 1
  let e ← IO.monoNanosNow
  let timeNs := e - s
  let timeMs := timeNs.toFloat / 1e6
  IO.println
    s!"GMM no matrix copy     time := {timeMs}ms \tloss := {loss}"

  IO.sleep 1000


  let s ← IO.monoNanosNow
  let loss := gradient alphas means logdiag lt x 1.0 1
  let e ← IO.monoNanosNow
  let timeNs := e - s
  let timeMs := timeNs.toFloat / 1e6
  IO.println
    s!"GMM gradient           time := {timeMs}ms \tloss := {loss.1.sum + loss.2.1.sum + loss.2.2.1.sum + loss.2.2.2.sum}"

  IO.sleep 1000
