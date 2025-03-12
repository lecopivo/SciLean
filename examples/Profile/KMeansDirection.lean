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

-- instance {X} [PlainDataType X] {I n} [IndexType I] [IdxType I n] : GetElem' (X^[I]) I X where
--   getElem xs i _ := xs.idxGet i

open Lean Parser Term in
macro (name:=minStx) "minᴵ" xs:funBinder* ", " b:term : term => do
  if xs.size = 1 then
    let x := xs[0]!
    `(IdxType.min fun $x => $b)
  else
    `(Function.argmin ↿fun $xs* => $b)

instance : Coe Nat USize := ⟨fun n => n.toUSize⟩


def kmeansDirSciLean {n k d : ℕ} [NeZero k]
    (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) : Float^[d]^[k] :=
  let x :=
      IndexType.Range.full.foldl
        (fun x i =>
          let x_1 := x.1;
          let dx := x.2;
          let a := IndexType.argMax fun j => -‖points[i] - centroids[j]‖₂[Float];
          let ydy₁ := centroids[a];
          let ydy₂ := (VectorType.const 1);
          let x₁₂₁ := x_1.1;
          let x₁₂₂ := x_1.2;
          let dx₁₂₁ := dx.1;
          let dx₁₂₂ := dx.2;
          let x₁ := points[i];
          let ydy₁ := x₁ - ydy₁;
          let ydy₂ := -ydy₂;
          let yn := ‖ydy₁‖₂[Float];
          let ydy₂_1 := ⟪ydy₁, ydy₂⟫[Float] / yn;
          let x₁ := -yn;
          let x₂ := -ydy₂_1;
          let x₁ := -x₁;
          let x₂ := -x₂;
          let ydy₁_1 := x₁₂₁ + x₁;
          let ydy₂_2 := dx₁₂₁ + x₂;
          let iy := yn⁻¹;
          let x₂ := -(iy ^ 2 * ydy₂_1);
          let ydy₁_2 := iy • ydy₁;
          let ydy₂ := iy • ydy₂ + x₂ • ydy₁;
          let ydy₁ := x₁₂₂[a];
          let ydy₂_3 := dx₁₂₂[a];
          let x₁ := -ydy₁_2;
          let x₂ := -ydy₂;
          let ydy₁ := ydy₁ + x₁;
          let ydy₂ := ydy₂_3 + x₂;
          let x₁ := setElem x₁₂₂ a ydy₁ True.intro;
          let x₂ := setElem dx₁₂₂ a ydy₂ True.intro;
          ((ydy₁_1, x₁), ydy₂_2, x₂))
        ((0, 0), 0);
    let y := x.1;
    let dy := x.2;
    let ydy₁ := y.2;
    let ydy₂ := dy.2;
    ydy₁ + ydy₂ -- VectorType.div ydy₁ ydy₂


def kmeansDirBestLeanImpl {n k d : ℕ} [NeZero k]
    (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) : Float^[d]^[k] := Id.run do

  let mut loss : Float := 0
  let mut J : Float^[d]^[k] := 0
  let mut sumJ : Float := 0
  let mut diagH : Float^[d]^[k] := 0

  for i in (IndexType.Range.full (I:=Idx n)) do
    let i := i.toFin

    let x_1 := (loss,J)
    let dx := (sumJ,diagH)
    let a := IndexType.argMax fun j => -‖points[i] - centroids[j]‖₂[Float];
    let ydy₁ := centroids[a];
    let ydy₂ := (VectorType.const 1);
    let x₁₂₁ := x_1.1;
    let x₁₂₂ := x_1.2;
    let dx₁₂₁ := dx.1;
    let dx₁₂₂ := dx.2;
    let x₁ := points[i];
    let ydy₁ := x₁ - ydy₁;
    let ydy₂ := -ydy₂;
    let yn := ‖ydy₁‖₂[Float];
    let ydy₂_1 := ⟪ydy₁, ydy₂⟫[Float] / yn;
    let x₁ := -yn;
    let x₂ := -ydy₂_1;
    let x₁ := -x₁;
    let x₂ := -x₂;
    let ydy₁_1 := x₁₂₁ + x₁;
    let ydy₂_2 := dx₁₂₁ + x₂;
    let iy := yn⁻¹;
    let x₂ := -(iy ^ 2 * ydy₂_1);
    let ydy₁_2 := iy • ydy₁;
    let ydy₂ := iy • ydy₂ + x₂ • ydy₁;
    let ydy₁ := x₁₂₂[a];
    let ydy₂_3 := dx₁₂₂[a];
    let x₁ := -ydy₁_2;
    let x₂ := -ydy₂;
    let ydy₁ := ydy₁ + x₁;
    let ydy₂ := ydy₂_3 + x₂;
    let x₁ := setElem x₁₂₂ a ydy₁ True.intro;
    let x₂ := setElem dx₁₂₂ a ydy₂ True.intro;
    loss := ydy₁_1
    J := x₁
    sumJ := ydy₂_2
    diagH := x₂
  return J + diagH -- VectorType.div J diagH



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

  let points : Float^[d]^[k] := ⟨⟨points.toByteArray, k, sorry_proof⟩, sorry_proof⟩
  let centroids : Float^[d]^[k] := ⟨⟨centroids.toByteArray, k, sorry_proof⟩, sorry_proof⟩

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
  let dir := kmeansDirBestLeanImpl points centroids
  let e ← IO.monoNanosNow
  let timeNs := e - s
  let timeMs := timeNs.toFloat / 1e6
  IO.println
    s!"best lean impl         time := {timeMs}ms \tdir norm := {‖dir‖₂²[Float]}"

  IO.sleep 1000


  let s ← IO.monoNanosNow
  let dir := kmeansDirSciLean points centroids
  let e ← IO.monoNanosNow
  let timeNs := e - s
  let timeMs := timeNs.toFloat / 1e6
  IO.println
    s!"SciLean impl           time := {timeMs}ms \tdir norm := {‖dir‖₂²[Float]}"
