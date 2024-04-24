import SciLean
import SciLean.Tactic.InferVar

open SciLean Scalar


----------------------------------------------------------------------------------------------------
-- Transformations and Reductions ------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

def map {I : Type} [IndexType I] (x : Float^[I]) (f : Float → Float) := Id.run do
  let mut x' := x
  for i in IndexType.univ I do
    x'[i] := f x'[i]
  return x'


/-- info: ⊞[1.000000, 1.414214, 1.732051] -/
#guard_msgs in
#eval ⊞[1.0,2.0,3.0].mapMono (fun x => sqrt x)

/-- info: ⊞[1.000000, 1.414214, 1.732051, 2.000000] -/
#guard_msgs in
#eval ⊞[1.0,2.0;3.0,4.0].mapMono (fun x => sqrt x)

/-- info: ⊞[0.000000, 1.000000, 1.414214, 1.732051, 2.000000, 2.236068, 2.449490, 2.645751] -/
#guard_msgs in
#eval (⊞ (i j k : Fin 2) => (IndexType.toFin (i,j,k)).toFloat).mapMono (fun x => sqrt x)

/-- info: ⊞[0.000000, 1.000000, 1.414214] -/
#guard_msgs in
#eval (0 : Float^[3]) |>.mapIdxMono (fun i _ => i.toFloat) |>.mapMono (fun x => sqrt x)


/-- info: 6.000000 -/
#guard_msgs in
#eval ⊞[(1.0 : Float),2.0,3.0].fold (·+·) 0

/-- info: 1.000000 -/
#guard_msgs in
#eval ⊞[(1.0 :Float),2.0,3.0].reduce (min · ·)


def softMax {I} [IndexType I]
  (r : Float) (x : Float^[I]) : Float^[I] := Id.run do
  let m := x.reduce (max · ·)
  let x := x.mapMono fun x => x-m
  let x := x.mapMono fun x => exp r*x
  let w := x.reduce (·+·)
  let x := x.mapMono fun x => x/w
  return x


def x := ⊞[(1.0:Float),2.0,3.0,4.0]
def A := ⊞[1.0,2.0;3.0,4.0]

/-- info: 10.000000 -/
#guard_msgs in
#eval ∑ i, x[i]

/-- info: 24.000000 -/
#guard_msgs in
#eval ∏ i, x[i]

/-- info: 10.000000 -/
#guard_msgs in
#eval ∑ i j, A[i,j]

/-- info: 24.000000 -/
#guard_msgs in
#eval ∏ i j, A[i,j]

def matMul {n m : Nat} (A : Float^[n,m]) (x : Float^[m]) :=
  ⊞ i => ∑ j, A[i,j] * x[j]

def trace {n : Nat} (A : Float^[n,n]) :=
  ∑ i, A[i,i]


----------------------------------------------------------------------------------------------------
-- Convolution and Operations on Indices -----------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- intentionally broken
-- def conv1d {n k : Nat} (x : Float^[n]) (w : Float^[k]) :=
--   ⊞ (i : Fin n) => ∑ j, w[j] * x[i-j]

def Fin.shift {n} (i : Fin n) (j : ℤ) : Fin n :=
    { val := ((i.1 + j) % n ).toNat, isLt := by sorry_proof }

def conv1d {n : Nat} (k : Nat) (w : Float^[[-k:k]]) (x : Float^[n]) :=
    ⊞ (i : Fin n) => ∑ j, w[j] * x[i.shift j.1]

def conv2d' {n m k : Nat} (w : Float^[[-k:k],[-k:k]]) (x : Float^[n,m]) :=
    ⊞ (i : Fin n) (j : Fin m) => ∑ a b, w[a,b] * x[i.shift a, j.shift b]

def conv2d {n m : Nat} (k : Nat) (J : Type) {I : Type} [IndexType I] [IndexType J] [DecidableEq J]
    (w : Float^[J,I,[-k:k],[-k:k]]) (b : Float^[J,n,m]) (x : Float^[I,n,m]) : Float^[J,n,m] :=
    ⊞ κ (i : Fin n) (j : Fin m) => b[κ,i,j] + ∑ ι a b, w[κ,ι,a,b] * x[ι, i.shift a, j.shift b]


----------------------------------------------------------------------------------------------------
-- Pooling and Difficulties with Dependent Types ---------------------------------------------------
----------------------------------------------------------------------------------------------------

def avgPool_v1 (x : Float^[n]) : Float^[n/2] :=
  ⊞ (i : Fin (n/2)) =>
    let i₁ : Fin n := ⟨2*i.1, by omega⟩
    let i₂ : Fin n := ⟨2*i.1+1, by omega⟩
    0.5 * (x[i₁] + x[i₂])


def avgPool_v2 (x : Float^[2*n]) : Float^[n] :=
  ⊞ (i : Fin n) =>
    let i₁ : Fin (2*n) := ⟨2*i.1, by omega⟩
    let i₂ : Fin (2*n) := ⟨2*i.1+1, by omega⟩
    0.5 * (x[i₁] + x[i₂])

def avgPool_v3 (x : Float^[n]) {m} (h : m = n/2 := by infer_var) : Float^[m] :=
  ⊞ (i : Fin m) =>
    let i1 : Fin n := ⟨2*i.1, by omega⟩
    let i2 : Fin n := ⟨2*i.1+1, by omega⟩
    0.5 * (x[i1] + x[i2])

def avgPool_v4 (x : Float^[n]) {m} (h : 2*m = n := by infer_var) : Float^[m] :=
  ⊞ (i : Fin m) =>
    let i1 : Fin n := ⟨2*i.1, by omega⟩
    let i2 : Fin n := ⟨2*i.1+1, by omega⟩
    0.5 * (x[i1] + x[i2])



/-- info: avgPool_v1 ⊞[1.0, 2.0, 3.0, 4.0, 5.0] : DataArrayN Float (Fin (5 / 2)) -/
#guard_msgs in
#check avgPool_v1 ⊞[1.0, 2.0, 3.0, 4.0, 5.0]

-- #check_failure avgPool_v2 ⊞[1.0, 2.0, 3.0, 4.0, 5.0]


/-- info: avgPool_v3 ⊞[1.0, 2.0, 3.0, 4.0, 5.0] ⋯ : DataArrayN Float (Fin 2) -/
#guard_msgs in
#check avgPool_v3 ⊞[1.0, 2.0, 3.0, 4.0, 5.0]

/-- info: ⊞[1.500000, 3.500000] -/
#guard_msgs in
#eval avgPool_v3 ⊞[1.0, 2.0, 3.0, 4.0, 5.0]


/-- info: avgPool_v4 ⊞[1.0, 2.0, 3.0, 4.0] ⋯ : DataArrayN Float (Fin 2) -/
#guard_msgs in
#check avgPool_v4 ⊞[1.0, 2.0, 3.0, 4.0]


/--
error: infer_var: discharger ` simp ` failed proving 2 * 2 = 5
---
info: avgPool_v4 ⊞[1.0, 2.0, 3.0, 4.0, 5.0] ⋯ : DataArrayN Float (Fin 2)
-/
#guard_msgs in
#check avgPool_v4 ⊞[1.0, 2.0, 3.0, 4.0, 5.0]

/-- info: ⊞[1.500000, 3.500000] -/
#guard_msgs in
#eval avgPool_v4 ⊞[1.0, 2.0, 3.0, 4.0]


variable {I} [IndexType I] [DecidableEq I]

def avgPool2d
    (x : Float^[I,n₁,n₂]) {m₁ m₂}
    (h₁ : m₁ = n₁/2 := by infer_var)
    (h₂ : m₂ = n₂/2 := by infer_var) : Float^[I,m₁,m₂] :=
  ⊞ (ι : I) (i : Fin m₁) (j : Fin m₂) =>
    let i₁ : Fin n₁ := ⟨2*i.1, by omega⟩
    let i₂ : Fin n₁ := ⟨2*i.1+1, by omega⟩
    let j₁ : Fin n₂ := ⟨2*j.1, by omega⟩
    let j₂ : Fin n₂ := ⟨2*j.1+1, by omega⟩
    0.5 * (x[ι,i₁,j₁] + x[ι,i₁,j₂] + x[ι,i₂,j₁] + x[ι,i₂,j₂])


----------------------------------------------------------------------------------------------------
-- Simple Neural Network ---------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

def dense (n : Nat) (A : Float^[n,I]) (b : Float^[n]) (x : Float^[I]) : Float^[n] :=
  ⊞ (i : Fin n) => b[i] + ∑ j, A[i,j] * x[j]

def SciLean.DataArrayN.resize3 (x : Float^[I]) (a b c : Nat) (h : a*b*c = IndexType.card I) :
    Float^[a,b,c] :=
  { data := x.data ,
    h_size := by simp[IndexType.card]; rw[← mul_assoc,←x.2,h] }

def nnet := fun (w₁,b₁,w₂,b₂,w₃,b₃) (x : Float^[28,28]) =>
  x |>.resize3 1 28 28 (by decide)
    |> conv2d 1 (Fin 8) w₁ b₁
    |>.mapMono (fun x => max x 0)
    |> avgPool2d (m₁:=14) (m₂:=14) -- infer_var does not work in this chain as expected :(
    |> dense 30 w₂ b₂
    |>.mapMono (fun x => max x 0)
    |> dense 10 w₃ b₃
    |> softMax 0.1
