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

set_default_scalar Float


/-- info: ⊞[⊞[1.000000, 2.000000], ⊞[3.000000, 4.000000]] -/
#guard_msgs in
#eval ⊞[⊞[1.0,2.0],⊞[3.0,4.0]]

/-- info: ⊞[⊞[-1.000000, -2.000000], ⊞[-3.000000, -4.000000]] -/
#guard_msgs in
#eval -⊞[⊞[1.0,2.0],⊞[3.0,4.0]]

/-- info: ⊞[⊞[11.000000, 102.000000], ⊞[1003.000000, 1004.000000]] -/
#guard_msgs in
#eval ⊞[⊞[1.0,2.0],⊞[3.0,4.0]] + ⊞[⊞[10.0,100.0],⊞[1000.0,1000.0]]

/-- info: ⊞[⊞[-9.000000, -98.000000], ⊞[-997.000000, -996.000000]] -/
#guard_msgs in
#eval ⊞[⊞[1.0,2.0],⊞[3.0,4.0]] - ⊞[⊞[10.0,100.0],⊞[1000.0,1000.0]]

/-- info: ⊞[⊞[1.000000, 2.000000], ⊞[10.000000, 100.000000]] -/
#guard_msgs in
#eval setElem ⊞[⊞[1.0,2.0],⊞[3.0,4.0]] (1 : Idx 2) ⊞[10.0,100.0] .intro

/-- info: ⊞[3.000000, 4.000000] -/
#guard_msgs in
#eval ⊞[⊞[1.0,2.0],⊞[3.0,4.0]][1]

/-- info: ⊞[⊞[1.000000, 1.000000], ⊞[1.000000, 1.000000]] -/
#guard_msgs in
#eval (VectorType.const 1 : Float^[2]^[2])

/-- info: ⊞[⊞[2.000000, 4.000000], ⊞[6.000000, 8.000000]] -/
#guard_msgs in
#eval 2 • ⊞[⊞[1.0,2.0],⊞[3.0,4.0]]


def kmeansDirSciLean {n k d : ℕ} [NeZero k]
    (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) : Float^[d]^[k] :=
  let x :=
      IndexType.Range.full.foldl
        (fun x i =>
          let x_1 := x.1;
          let dx := x.2;
          let a := IdxType.argMax fun j => -‖points[i] - centroids[j]‖₂²;
          let ydy₁ := centroids[a];
          let ydy₂ := (VectorType.const 1);
          let x₁₂₁ := x_1.1;
          let x₁₂₂ := x_1.2;
          let dx₁₂₁ := dx.1;
          let dx₁₂₂ := dx.2;
          let x₁ := points[i];
          let ydy₁ := x₁ - ydy₁;
          let ydy₂ := -ydy₂;
          let ydy₁_1 := ‖ydy₁‖₂²;
          let ydy₂_1 := 2 * ⟪ydy₁, ydy₂⟫;
          let x₁ := -ydy₁_1;
          let x₂ := -ydy₂_1;
          let x₁ := -x₁;
          let x₂ := -x₂;
          let ydy₁_2 := x₁₂₁ + x₁;
          let ydy₂_2 := dx₁₂₁ + x₂;
          let ydy₁ := 2 • ydy₁;
          let ydy₂ := 2 • ydy₂;
          let ydy₁_3 := x₁₂₂[a];
          let ydy₂_3 := dx₁₂₂[a];
          let x₁ := -ydy₁;
          let x₂ := -ydy₂;
          let ydy₁ := ydy₁_3 + x₁;
          let ydy₂ := ydy₂_3 + x₂;
          let x₁ := setElem x₁₂₂ a ydy₁ True.intro;
          let x₂ := setElem dx₁₂₂ a ydy₂ True.intro;
          ((ydy₁_2, x₁), ydy₂_2, x₂))
        ((0, 0), 0);
    let y := x.1;
    let dy := x.2;
    let ydy₁ := y.2;
    let ydy₂ := dy.2;
    ydy₁ + ydy₂ --- VectorType.div ydy₁ ydy₂


def _root_.SciLean.DataArrayN.idxSet {I n} [IndexType I] [IdxType I n] (x : Float^[I]) (i : I) (val : Float) : Float^[I] :=

  let data := x.1.1.toFloatArray sorry_proof
  let data := data.uset (toIdx i) val sorry_proof
  ⟨⟨data.toByteArray, sorry_proof⟩, sorry_proof⟩


def kmeansDirBestLeanImpl {n k d : ℕ} [NeZero k]
    (points : Float^[Idx n, Idx d]) (centroids : Float^[Idx k, Idx d]) : Float^[Idx k, Idx d] := Id.run do

  let mut J : Float^[Idx k, Idx d] := 0
  let mut diagH : Float^[Idx k, Idx d] := 0

  for i in (IndexType.Range.full (I:=Idx n)) do

    let F := fun (i : Idx n) (j : Idx k) (l : Idx d) => points.idxGet (i,l) - centroids.idxGet (j,l)

    let a := IdxType.argMin fun (j : Idx k) =>
      ∑ᴵ (l : Idx d), (F i j l)^2

    for l in (IndexType.Range.full (I:=Idx d)) do
      diagH := (diagH.idxSet (a,l) (diagH.idxGet (a,l) + 2.0))

      let dJ := 2 • (centroids.idxGet (a,l) - points.idxGet (i,l))
      J := (J.idxSet (a,l) (J.idxGet (a,l) + dJ))

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
  let dir := kmeansDirSciLean points centroids
  let e ← IO.monoNanosNow
  let timeNs := e - s
  let timeMs := timeNs.toFloat / 1e6
  IO.println
    s!"SciLean impl           time := {timeMs}ms \tdir norm := {‖dir‖₂²[Float]}"
