import SciLean
import SciLean.Data.IndexType.RangeNotation

open SciLean

def rand01 : IO Float := do
  let N : Nat := 10^16
  let i ← IO.rand 0 N
  return i.toFloat / N.toFloat

def FloatArray.rand01 (n : Nat) : IO FloatArray := do
  let mut xs : FloatArray := .mkEmpty n
  for _ in [0:n] do
    xs := xs.push (← _root_.rand01)
  return xs


set_default_scalar Float

-- @[inline]
-- def SciLean.DataArrayN.setFloatUnsafe (xs : Float^[m,n]) (i : Idx m) (j : Idx n) (v : Float) : Float^[m,n] :=
--   let data : ByteArray := cast sorry_proof xs
--   let data := data.usetFloatUnsafe (toIdx (i,j)) v sorry_proof
--   cast sorry_proof data


def SciLean.DataArrayN.mkExclusive {X} [PlainDataType X] {I n} [IndexType I n]
    (xs : X^[I]) (uniqueName : Name) : X^[I] :=
  -- let i : I := fromIdx ⟨0,sorry_proof⟩
  -- setElem xs i xs[i] .intro
  let data : ByteArray := cast sorry_proof xs
  let data := data.mkExclusive uniqueName
  cast sorry_proof data

-- #eval
--   let a := ⊞[1.0,2;3,4]
--   let b := a.setFloatUnsafe 1 1 100
--   let c := b.setFloatUnsafe 0 1 42
--   (a,b,c)

-- @[inline]
-- def SciLean.DataArrayN.addFloatUnsafe (xs : Float^[m,n]) (i : Idx m) (j : Idx n) (v : Float) : Float^[m,n] :=
--   let vi := xs[i,j]
--   let data : ByteArray := cast sorry_proof xs
--   let data := data.usetFloatUnsafe (toIdx (i,j)) (vi + v) sorry_proof
--   cast sorry_proof data


@[extern "scilean_kmeans_direction"]
opaque kmeansDirCImpl (d n k : USize) (points : ByteArray) (centroids : ByteArray) : ByteArray

def kmeansDirC {n k d : ℕ} (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) : Float^[d]^[k] :=
  cast sorry_proof (kmeansDirCImpl d.toUSize n.toUSize k.toUSize points.1.1 centroids.1.1)

def kmeansDirSciLean {n k d : ℕ} [NeZero k]
    (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) : Float^[d]^[k] :=
  let x :=
    IndexType.fold IndexType.Range.full (0, 0)
      fun (i : Idx n) (xdx : (Float^[d]^[k]×Float^[d]^[k])) =>
      let x := xdx.1;
      let dx := xdx.2;
      let a := argMinᴵ (j : Idx k), ‖points[i] - centroids[j]‖₂²;
      let ydy₁ := centroids[a];
      let ydy₂ : Float^[d] := .replicate (Idx d) (1.0)
      let x₁ := points[i];
      let ydy₁ := x₁ - ydy₁;
      let ydy₂ := -ydy₂;
      let ydy₁ := 2 • ydy₁;
      let ydy₂ := 2 • ydy₂;
      let ydy₁_1 := x[a];
      let ydy₂_1 := dx[a];
      let ydy₁ := -ydy₁;
      let ydy₂ := -ydy₂;
      let ydy₁ := ydy₁_1 + ydy₁;
      let ydy₂ := ydy₂_1 + ydy₂;
      let x₁ := setElem x a ydy₁ True.intro;
      let x₂ := setElem dx a ydy₂ True.intro;
      (x₁, x₂);
  let x_1 := x.1;
  let dx := x.2;
  x_1 + dx -- VectorType.div x_1 dx


def kmeansDirSciLeanNoBLAS {n k d : ℕ} [NeZero k]
    (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) : Float^[d]^[k] :=
  let x :=
    IndexType.fold IndexType.Range.full (0, 0) fun (i : Idx n) xdx =>
      let x := xdx.1;
      let dx := xdx.2;
      let a := argMinᴵ (j : Idx k), ∑ᴵ (l : Idx d), (points[(i, l)] - centroids[(j, l)]) ^ 2;
      let x :=
        IndexType.fold IndexType.Range.full (x, dx)
          fun (i_1 : Idx d) (xdx : (Float^[d]^[k]×Float^[d]^[k])) =>
          let x := xdx.1;
          let dx := xdx.2;
          let x₁ := centroids[(a, i_1)];
          let x₂ := 1.0;
          let x₁_1 := points[(i, i_1)];
          let ydy₁ := x₁_1 - x₁;
          let ydy₂ := -x₂;
          let ydy₁_1 := x[(a, i_1)];
          let ydy₂_1 := dx[(a, i_1)];
          let x₁ := 2 * ydy₁;
          let x₂ := 2 * ydy₂;
          let ydy₁ := -x₁;
          let ydy₂ := -x₂;
          let ydy₁ := ydy₁_1 + ydy₁;
          let ydy₂ := ydy₂_1 + ydy₂;
          let x₁ := setElem x (a, i_1) ydy₁ True.intro;
          let x₂ := setElem dx (a, i_1) ydy₂ True.intro;
          (x₁, x₂);
      let x_1 := x.1;
      let dx := x.2;
      (x_1, dx);
  let x_1 := x.1;
  let dx := x.2;
  x_1 + dx -- VectorType.div x_1 dx


@[inline]
def _root_.SciLean.DataArrayN.idxGet {X} [pd : PlainDataType X] {I n} [IndexType I] [IndexType I n]
    (xs : X^[I]) (i : I) : X :=
  xs[i]
  -- pd.fromByteArray xs.1.1 (toIdx i) sorry_proof

@[inline]
def _root_.SciLean.DataArrayN.idxSet {I n} [IndexType I] [IndexType I n] (x : Float^[I]) (i : I) (val : Float) : Float^[I] :=
  setElem x i val .intro
  -- let data := x.1.1.toFloatArray sorry_proof
  -- let data := data.uset (toIdx i) val sorry_proof
  -- ⟨⟨data.toByteArray, sorry_proof⟩, sorry_proof⟩


def kmeansDirBestLeanImpl {n k d : ℕ}
    (points : Float^[Idx n, Idx d]) (centroids : Float^[Idx k, Idx d]) : Float^[Idx k, Idx d] := Id.run do

  let mut J : Float^[Idx k, Idx d] := 0
  let mut diagH : Float^[Idx k, Idx d] := 0

  -- J := J.mkExclusive `J
  -- diagH := diagH.mkExclusive `diagH

  for i in [:n] do

    let mut minj : Idx k := ⟨0,sorry_proof⟩
    let mut minNorm : Float := Float.inf

    for j in [:k] do

      let mut norm : Float := 0.0

      for l in [:d] do
        norm := norm + (points[i,l] - centroids[j,l])^2

      if norm < minNorm then
        minj := j
        minNorm := norm

    for l in [:d] do
      -- diagH := diagH.setFloatUnsafe minj l (diagH[minj,l] + 2.0)
      -- J := J.setFloatUnsafe minj l (J[minj,l] + 2 • (centroids[minj,l] - points[i,l]))
      diagH[minj,l] += 2.0
      J[minj,l] += 2 • (centroids[minj,l] - points[i,l])

  for j in [:k] do
    for l in [:d] do
      J[j,l] += diagH[j,l]

  return J -- VectorType.div J diagH


-- todo: rewrite this in terms of `FloatArray` to have a really raw Lean implementation
def kmeansDirBestLeanImpl' {n k d : ℕ} [NeZero k]
    (points : Float^[Idx n, Idx d]) (centroids : Float^[Idx k, Idx d]) : Float^[Idx k, Idx d] := Id.run do

  let mut J : Float^[Idx k, Idx d] := 0
  let mut diagH : Float^[Idx k, Idx d] := 0

  J := J.mkExclusive `J
  diagH := diagH.mkExclusive `diagH

  for i in [:n] do

    let a := IndexType.argMin fun (j : Idx k) =>
      ∑ᴵ (l : Idx d), (points[i,l] - centroids[j,l])^2

    for l in [:d] do
      -- diagH := diagH.setFloatUnsafe a l (diagH[a,l] + 2.0)
      -- J := J.setFloatUnsafe a l (J[a,l] + 2 • (centroids[a,l] - points[i,l]))
      diagH[a,l] += 2.0
      J[a,l] += 2 • (centroids[a,l] - points[i,l])


  return J + diagH -- VectorType.div J diagH



def main : IO Unit := do

  let d := 16
  let n := 10000
  let k := 1000

  IO.setRandSeed 0
  let points ← FloatArray.rand01 (n*d)
  let centroids ← FloatArray.rand01 (k*d)

  IO.println
    s!"k-means profile test\n\
       k := {k}, n := {n}, d := {d}"
  IO.println ""

  let points : Float^[d]^[n] := cast sorry_proof points.toByteArray
  let centroids : Float^[d]^[k] := cast sorry_proof centroids.toByteArray

  let s ← IO.monoNanosNow
  let dir := kmeansDirC points centroids
  let e ← IO.monoNanosNow
  let timeNs := e - s
  let timeMs := timeNs.toFloat / 1e6
  IO.println
    s!"c implementation       time := {timeMs}ms \tdir norm := {‖dir‖₂²[Float]}"

  IO.sleep 1000

  -- this should be reference C implementation
  -- let s ← IO.monoNanosNow
  -- let loss := kmeansForLoop_cimpl d n k points centroids
  -- let e ← IO.monoNanosNow
  -- let timeNs := e - s
  -- let timeMs := timeNs.toFloat / 1e6
  -- IO.println
  --   s!"reference c impl       time := {timeMs}ms \tloss := {loss}"

  -- IO.sleep 1000


  -- this should be the best possible Lean implementation
  let s ← IO.monoNanosNow
  let dir := kmeansDirBestLeanImpl (points.uncurry) (centroids.uncurry)
  let e ← IO.monoNanosNow
  let timeNs := e - s
  let timeMs := timeNs.toFloat / 1e6
  IO.println
    s!"best lean impl         time := {timeMs}ms \tdir norm := {‖dir‖₂²[Float]}"

  IO.sleep 1000


  let s ← IO.monoNanosNow
  let dir := kmeansDirSciLeanNoBLAS points centroids
  let e ← IO.monoNanosNow
  let timeNs := e - s
  let timeMs := timeNs.toFloat / 1e6
  IO.println
    s!"SciLean no BLAS        time := {timeMs}ms \tdir norm := {‖dir‖₂²[Float]}"

  IO.sleep 1000

  -- let s ← IO.monoNanosNow
  -- let dir := kmeansDirSciLean points centroids
  -- let e ← IO.monoNanosNow
  -- let timeNs := e - s
  -- let timeMs := timeNs.toFloat / 1e6
  -- IO.println
  --   s!"SciLean impl           time := {timeMs}ms \tdir norm := {‖dir‖₂²[Float]}"
