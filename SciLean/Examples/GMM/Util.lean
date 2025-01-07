import SciLean

open Lean IO

namespace SciLean.Examples.GMM

open SciLean

def parseFloat (s : String) : Except String Float :=
  match Lean.Json.parse s with
    | .ok (.num t) => .ok t.toFloat
    | _ => throw "Failed to parse as float."

def _root_.String.toFloat! (s : String) : Float :=
  match parseFloat s with
  | .ok x => x
  | _ => panic! s!"not a float {s}"

open Lean System


local macro (priority:=high+1) "Float^[" M:term ", " N:term "]" : term =>
  `(FloatMatrix' .RowMajor .normal (Fin $M) (Fin $N))

local macro (priority:=high+1) "Float^[" N:term "]" : term =>
  `(FloatVector (Fin $N))

-- notation: `v[i] := vᵢ`
local macro (priority:=high+10) id:ident noWs "[" i:term "]" " := " v:term : doElem =>
   `(doElem| $id:ident := VectorType.set $id $i $v)

-- notation: `A[i,:] := r`
local macro (priority:=high+10) id:ident noWs "[" i:term "," ":" "]" " := " v:term : doElem =>
   `(doElem| $id:ident := MatrixType.updateRow $id $i $v)

-- notation: `⊞ i => vᵢ`
open Lean Parser Term in
scoped macro (priority:=high+10) "⊞" i:funBinder " => " b:term : term =>
   `(term| VectorType.fromVec  fun $i => $b)


structure GMMData (D K N : Nat) where
  m : Nat
  γ : Float
  x : Float^[N,D]
  α : Float^[K]
  μ : Float^[K,D]
  q : Float^[K,D]
  l : Float^[K,(D-1)*D/2]


def loadData (D K N : Nat) : IO (GMMData D K N) := do

  unless N = 1000 do throw (.userError s!"only N=1000 is currently supported!")

  let path := (← IO.currentDir) / "SciLean" / "Examples" / "GMM" / "data" / s!"gmm_d{D}_K{K}.txt"

  IO.FS.withFile path .read fun file => do
    let mut line : String := (← file.getLine) |>.stripSuffix "\n"
    let dims := line.splitOn " " |>.map (fun s => String.toNat! s)
    IO.println s!"{dims}"
    let D' := dims[0]!
    let K' := dims[1]!
    let N' := dims[2]!
    unless D = D' do throw (.userError s!"invalid D, specified {D}, in file {D'}")
    unless K = K' do throw (.userError s!"invalid D, specified {K}, in file {K'}")
    unless N = N' do throw (.userError s!"invalid D, specified {N}, in file {N'}")

    -- read α
    let mut α : Float^[K] := 0
    for i in fullRange (Fin K) do
      line := (← file.getLine) |>.stripSuffix "\n"
      α[i] := line.toFloat!

    -- read μ
    let mut μ : Float^[K,D] := 0
    for i in fullRange (Fin K) do
      let vals := (← file.getLine) |>.stripSuffix "\n" |>.stripSuffix " " |>.splitOn |>.map (·.toFloat!) |>.toArray
      let μᵢ := ⊞ (i : Fin D) => (vals[i]! : Float)
      μ[i,:] := μᵢ

    let mut q : Float^[K,D] := 0
    let mut l : Float^[K,(D-1)*D/2] := 0

    for i in fullRange (Fin K) do
      let vals := (← file.getLine) |>.stripSuffix "\n" |>.stripSuffix " " |>.splitOn |>.map (·.toFloat!) |>.toArray
      q[i,:] := ⊞ i => vals[i]!
      l[i,:] := ⊞ i => vals[i.1+D]!

    let mut x : Float^[N,D] := 0

    for i in fullRange (Fin N) do
      let vals := (← file.getLine) |>.stripSuffix "\n" |>.stripSuffix " " |>.splitOn |>.map (·.toFloat!) |>.toArray
      x[i,:] := ⊞ i => vals[i.1]!

    let vals := (← file.getLine) |>.stripSuffix "\n" |>.stripSuffix " " |>.splitOn |>.map (·.toFloat!) |>.toArray

    let γ := vals[0]!
    let m := vals[1]!.toUInt64.toNat

    return {
      m := m
      γ := γ
      x := x
      α := α
      μ := μ
      q := q
      l := l
    }
