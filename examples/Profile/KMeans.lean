import SciLean

open SciLean

def rand01 : IO Float := do
  let N : Nat := 10^16
  let i ← IO.rand 0 N
  return i.toFloat / N.toFloat

def Float.inf := 1.0/0.0

def FloatArray.rand01 (n : Nat) : IO FloatArray := do
  let mut xs : FloatArray := .mkEmpty n
  for _ in [0:n] do
    xs := xs.push (← _root_.rand01)
  return xs


@[inline]
def _root_.SciLean.DataArrayN.idxGet {X} [pd : PlainDataType X] {I n} [IndexType I] [IdxType I n]
    (xs : X^[I]) (i : I) : X :=
  pd.fromByteArray xs.1.1 (toIdx i) sorry_proof

instance : Coe Nat USize := ⟨fun n => n.toUSize⟩

@[extern "scilean_kmeans"]
opaque kmeansForLoop_cimpl (d n k : USize) (points centroids : @& FloatArray) : Float

def kmeansBestLeanImpl (d n k : Nat) (points centroids : FloatArray) : Float := Id.run do
  let mut loss := 0.0
  for i in IndexType.Range.full (I:=Idx n) do

    let mut minNorm2 := Float.inf

    for j in IndexType.Range.full (I:=Idx k) do

      let mut norm2 := 0.0
      for l in IndexType.Range.full (I:=Idx d) do
        let xil := points.uget (i.1*d.toUSize + l.1) sorry_proof
        let cjl := centroids.uget (j.1*d.toUSize + l.1) sorry_proof
        norm2 := norm2 + (xil - cjl)*(xil - cjl)

      if norm2 < minNorm2 then
        minNorm2 := norm2

    loss := loss + minNorm2
  return loss


def kmeansByteArrayProblem (d n k : Nat) (points centroids : FloatArray) : Float := Id.run do
  let points := points.toByteArray
  let centroids := centroids.toByteArray
  let mut loss := 0.0
  for i in IndexType.Range.full (I:=Idx n) do

    let mut minNorm2 := Float.inf

    for j in IndexType.Range.full (I:=Idx k) do

      let mut norm2 := 0.0
      for l in IndexType.Range.full (I:=Idx d) do
        let xil := points.ugetFloat (i.1*d.toUSize + l.1) sorry_proof
        let cjl := centroids.ugetFloat (j.1*d.toUSize + l.1) sorry_proof
        norm2 := norm2 + (xil - cjl)*(xil - cjl)

      if norm2 < minNorm2 then
        minNorm2 := norm2

    loss := loss + minNorm2
  return loss


def kmeansSciLean_no_blas (d n k : Nat) (points centroids : FloatArray) : Float :=

  let points : Float^[Idx d]^[Idx n] := ⟨⟨points.toByteArray, n, sorry_proof⟩, sorry_proof⟩
  let centroids : Float^[Idx d]^[Idx k] := ⟨⟨centroids.toByteArray, n, sorry_proof⟩, sorry_proof⟩

  ∑'' (i : Idx n), IdxType.min (fun (j : Idx k) => ∑'' (l : Idx d),
     let xil := points.uncurry.idxGet (i,l)
     let cjl := centroids.uncurry.idxGet (j,l)
     (xil - cjl)^2)


def kmeansSciLean (d n k : Nat) (points centroids : FloatArray) : Float :=

  let points : Float^[d]^[n] := ⟨⟨points.toByteArray, n, sorry_proof⟩, sorry_proof⟩
  let centroids : Float^[d]^[k] := ⟨⟨centroids.toByteArray, n, sorry_proof⟩, sorry_proof⟩
  ∑ i, IndexType.min (fun j => ‖points[i] - centroids[j]‖₂²[Float])

def main : IO Unit := do

  let d := 16
  let n := 10000
  let k := 1000

  let points ← FloatArray.rand01 (n*d)
  let centroids ← FloatArray.rand01 (k*d)

  IO.println
    s!"k-means profile test\n\
       k := {k}, n := {n}, d := {d}"
  IO.println ""


  -- this should be reference C implementation
  let s ← IO.monoNanosNow
  let loss := kmeansForLoop_cimpl d n k points centroids
  let e ← IO.monoNanosNow
  let timeNs := e - s
  let timeMs := timeNs.toFloat / 1e6
  IO.println
    s!"reference c impl       time := {timeMs}ms \tloss := {loss}"

  IO.sleep 1000


  -- this should be the best possible Lean implementation
  let s ← IO.monoNanosNow
  let loss := kmeansBestLeanImpl d n k points centroids
  let e ← IO.monoNanosNow
  let timeNs := e - s
  let timeMs := timeNs.toFloat / 1e6
  IO.println
    s!"best lean impl         time := {timeMs}ms \tloss := {loss}"

  IO.sleep 1000

  -- just switching from `FloatArray` to `ByteArray` cases issue
  -- I have no idea what is going wrong here
  -- This is the main slow down
  let s ← IO.monoNanosNow
  let loss := kmeansByteArrayProblem d n k points centroids
  let e ← IO.monoNanosNow
  let timeNs := e - s
  let timeMs := timeNs.toFloat / 1e6
  IO.println
    s!"ByteArray issue        time := {timeMs}ms \tloss := {loss}"

  IO.sleep 1000

  let s ← IO.monoNanosNow
  let loss := kmeansSciLean_no_blas d n k points centroids
  let e ← IO.monoNanosNow
  let timeNs := e - s
  let timeMs := timeNs.toFloat / 1e6
  IO.println
    s!"scilean no BLAS        time := {timeMs}ms \tloss := {loss}"

  IO.sleep 1000

  -- this is the implementation we want to use
  let s ← IO.monoNanosNow
  let loss := kmeansSciLean d n k points centroids
  let e ← IO.monoNanosNow
  let timeNs := e - s
  let timeMs := timeNs.toFloat / 1e6
  IO.println
    s!"target scilean impl    time := {timeMs}ms \tloss := {loss}"

  IO.sleep 1000


  -- let s ← IO.monoNanosNow
  -- let loss := kmeansForLoop d n k points centroids
  -- let e ← IO.monoNanosNow
  -- let timeNs := e - s
  -- let timeMs := timeNs.toFloat / 1e6
  -- IO.println
  --   s!"for loop               time := {timeMs}ms \tloss := {loss}"
  -- IO.sleep 1000


  -- IO.sleep 1000

  -- let s ← IO.monoNanosNow
  -- let loss := kmeansSciLean_idx_fold d n k points centroids
  -- let e ← IO.monoNanosNow
  -- let timeNs := e - s
  -- let timeMs := timeNs.toFloat / 1e6
  -- IO.println
  --   s!"scilean idx fold       time := {timeMs}ms \tloss := {loss}"

  -- IO.sleep 1000

  -- let s ← IO.monoNanosNow
  -- let loss := kmeansIdxFold d n k points centroids
  -- let e ← IO.monoNanosNow
  -- let timeNs := e - s
  -- let timeMs := timeNs.toFloat / 1e6
  -- IO.println
  --   s!"idx fold               time := {timeMs}ms \tloss := {loss}"

  -- IO.sleep 1000
