import SciLean

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


def kmeansDirSciLean {n k d : ℕ} [NeZero k]
    (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) : Float^[d]^[k] :=
  let x :=
    IdxType.fold IndexType.Range.full (0, 0)
      fun (i : Idx n) (xdx : (Float^[d]^[k]×Float^[d]^[k])) =>
      let x := xdx.1;
      let dx := xdx.2;
      let a := argMinᴵ (j : Idx k), ‖points[i] - centroids[j]‖₂²;
      let ydy₁ := centroids[a];
      let ydy₂ : Float^[d] := (VectorType.const (1.0));
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
    IdxType.fold IndexType.Range.full (0, 0) fun (i : Idx n) xdx =>
      let x := xdx.1;
      let dx := xdx.2;
      let a := argMinᴵ (j : Idx k), ∑ᴵ (l : Idx d), (points[(i, l)] - centroids[(j, l)]) ^ 2;
      let x :=
        IdxType.fold IndexType.Range.full (x, dx)
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
def _root_.SciLean.DataArrayN.idxGet {X} [pd : PlainDataType X] {I n} [IndexType I] [IdxType I n]
    (xs : X^[I]) (i : I) : X :=
  xs[i]
  -- pd.fromByteArray xs.1.1 (toIdx i) sorry_proof

@[inline]
def _root_.SciLean.DataArrayN.idxSet {I n} [IndexType I] [IdxType I n] (x : Float^[I]) (i : I) (val : Float) : Float^[I] :=
  setElem x i val .intro
  -- let data := x.1.1.toFloatArray sorry_proof
  -- let data := data.uset (toIdx i) val sorry_proof
  -- ⟨⟨data.toByteArray, sorry_proof⟩, sorry_proof⟩

-- todo: rewrite this in terms of `FloatArray` to have a really raw Lean implementation
def kmeansDirBestLeanImpl {n k d : ℕ} [NeZero k]
    (points : Float^[Idx n, Idx d]) (centroids : Float^[Idx k, Idx d]) : Float^[Idx k, Idx d] := Id.run do

  let mut J : Float^[Idx k, Idx d] := 0
  let mut diagH : Float^[Idx k, Idx d] := 0

  for i in (IndexType.Range.full (I:=Idx n)) do

    let a := IdxType.argMin fun (j : Idx k) =>
      ∑ᴵ (l : Idx d), (points[i,l] - centroids[j,l])^2

    for l in (IndexType.Range.full (I:=Idx d)) do
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

  let s ← IO.monoNanosNow
  let dir := kmeansDirSciLean points centroids
  let e ← IO.monoNanosNow
  let timeNs := e - s
  let timeMs := timeNs.toFloat / 1e6
  IO.println
    s!"SciLean impl           time := {timeMs}ms \tdir norm := {‖dir‖₂²[Float]}"
