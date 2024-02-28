import SciLean.Data.Int64
import Mathlib.Control.Random

open SciLean

structure RandGenInt64 where
  s1 : Int64
  s2 : Int64

instance : Inhabited RandGenInt64 := ⟨{ s1 := 0, s2 := 0 }⟩

namespace RandGenInt64

structure Int2 where
  fst : Int64
  snd : Int64

structure IntGen where
  val : Int64
  gen : RandGenInt64

structure Gen2 where
  fst : RandGenInt64
  snd : RandGenInt64

def range := (1, 2147483562)

instance : Repr RandGenInt64 where
  reprPrec | ⟨s1, s2⟩, _ => Std.Format.bracket "⟨" (toString s1 ++ ", " ++ toString s2) "⟩"

@[inline]
def next : RandGenInt64 → IntGen
  | ⟨s1, s2⟩ =>
    let s1   : Int64 := s1
    let s2   : Int64 := s2
    let k    : Int64 := s1 / 53668
    let s1'  : Int64 := 40014 * ((s1 : Int64) - k * 53668) - k * 12211
    let s1'' : Int64 := if s1' < 0 then s1' + 2147483563 else s1'
    let k'   : Int64 := s2 / 52774
    let s2'  : Int64 := 40692 * ((s2 : Int64) - k' * 52774) - k' * 3791
    let s2'' : Int64 := if s2' < 0 then s2' + 2147483399 else s2'
    let z    : Int64 := s1'' - s2''
    let z'   : Int64 := if z < 1 then z + 2147483562 else z % 2147483562
    ⟨z', ⟨s1'', s2''⟩⟩

def split : RandGenInt64 → Gen2
  | g@⟨s1, s2⟩ =>
    let newS1  := if s1 = 2147483562 then 1 else s1 + 1
    let newS2  := if s2 = 1          then 2147483398 else s2 - 1
    let newG   := (next g).2
    let leftG  := RandGenInt64.mk newS1 newG.2
    let rightG := RandGenInt64.mk newG.1 newS2
    ⟨leftG, rightG⟩

-- instance : RandomGen RandGenInt64 := {
--   range  := fun _ => stdRange,
--   next   := stdNext,
--   split  := stdSplit
-- }


-- abbrev RandInt64 := StateM RandGenInt64

end RandGenInt64

open RandGenInt64 in
def randGenTest (n : Nat) : IO Unit := do

  let mut g : RandGenInt64 := ⟨1,1⟩
  let mut score : Array Float := .mkArray 10 0

  for i in [0:n] do
    let xg := next g
    let x := xg.1
    g := xg.2
    let i := x % 10
    score := score.set! i.toNat (1 + score.get! i.toNat)

  score := score.map (fun x => 10 * x / n.toFloat)
  IO.println score



def randStdGenTest (n : Nat) : IO Unit := do

  let mut g : StdGen := ⟨1,1⟩
  let mut score : Array Float := .mkArray 10 0

  for i in [0:n] do
    let xg := stdNext g
    let x := xg.1
    g := xg.2
    let i := x % 10
    score := score.set! i (1 + score.get! i)

  score := score.map (fun x => 10 * x / n.toFloat)
  IO.println score


def randStdGenNatTest (n : Nat) : IO Unit := do

  let mut g : StdGen := ⟨1,1⟩
  let mut score : Array Float := .mkArray 10 0

  for i in [0:n] do
    let xg := randNat g 0 1000000000000000
    let x := xg.1
    g := xg.2
    let i := x % 10
    score := score.set! i (1 + score.get! i)

  score := score.map (fun x => 10 * x / n.toFloat)
  IO.println score




def randMathlibTest (n : Nat) : IO Unit := do

  let mut g : StdGen := ⟨1,1⟩
  let mut score : Array Float := .mkArray 10 0

  for i in [0:n] do
    let xg := Random.randFin (n:=1000000000000000) (m:=Id) (g:=StdGen) (ULift.up g)
    let x := xg.1
    g := ULift.down xg.2
    let i := x % 10
    score := score.set! i (1 + score.get! i)

  score := score.map (fun x => 10 * x / n.toFloat)
  IO.println score
