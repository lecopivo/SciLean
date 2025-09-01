import SciLean.Data.DataArray.DataArray
import SciLean.Data.Int64
import Mathlib.Control.Random

namespace SciLean

open Random


structure Int64Gen where
  s1 : USize
  s2 : USize

instance : Inhabited Int64Gen := ⟨{ s1 := 0, s2 := 0 }⟩

def stdRange := (1, 2147483562)

instance : Repr Int64Gen where
  reprPrec | ⟨s1, s2⟩, _ => Std.Format.bracket "⟨" (repr s1 ++ ", " ++ repr s2) "⟩"

def stdNext : Int64Gen → Nat × Int64Gen
  | ⟨s1, s2⟩ =>
    let s1   : Int64 := s1.toInt64
    let s2   : Int64 := s2.toInt64
    let k    : Int64 := s1 / 53668
    let s1'  : Int64 := 40014 * ((s1 : Int64) - k * 53668) - k * 12211
    let s1'' : Int64 := if s1' < 0 then s1' + 2147483563 else s1'
    let k'   : Int64 := s2 / 52774
    let s2'  : Int64 := 40692 * ((s2 : Int64) - k' * 52774) - k' * 3791
    let s2'' : Int64 := if s2' < 0 then s2' + 2147483399 else s2'
    let z    : Int64 := s1'' - s2''
    let z'   : Int64 := if z < 1 then z + 2147483562 else z % (2147483562 : Int64)
    (z'.toNatClampNeg, ⟨s1''.toUSize, s2''.toUSize⟩)
    -- (s1.toNat, ⟨s1,s2⟩)

def stdSplit : Int64Gen → Int64Gen × Int64Gen
  | g@⟨s1, s2⟩ =>
    let newS1  := if s1 = 2147483562 then 1 else s1 + 1
    let newS2  := if s2 = 1          then 2147483398 else s2 - 1
    let newG   := (stdNext g).2
    let leftG  := Int64Gen.mk newS1 newG.2
    let rightG := Int64Gen.mk newG.1 newS2
    (leftG, rightG)

instance : RandomGen Int64Gen := {
  range  := fun _ => stdRange,
  next   := stdNext,
  split  := stdSplit
}

def mkInt64Gen (s : USize := 0) : Int64Gen :=
  let q  := s / 2147483562
  let s1 := s % 2147483562
  let s2 := q % 2147483398
  ⟨s1 + 1, s2 + 1⟩

instance : Random Id Float where
  random := do
    let N := 1000000000000 -- 1e12
    let n ← randBound Nat 0 N (by decide)
    let x := n.1.toUSize.toNat.toFloat / N.toUSize.toNat.toFloat
    let x := 2*x - 1
    return x

instance [Random Id α] [Random Id β] : Random Id (α × β) where
  random := do
    let a ← rand α
    let b ← rand β
    return (a,b)

-- open Random
-- instance
--     {I : Type} {nI} [IndexType I nI] [Fold I]
--     {R : Type} [PlainDataType R] [Random Id R] [Zero R] :
--     Random Id (R^[I]) where
--   random :=
--     let x : R^[I] := Id.run do
--       let mut x : DataArray R := DataArray.mkEmpty nI
--       for i in fullRange I do
--         x := x.push (← random (α:=R))
--         -- x := ArrayType.set x i (← random (α:=R))
--       return ⟨x, nI, sorry_proof⟩
--     sorry
