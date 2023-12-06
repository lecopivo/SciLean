import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Defs

import SciLean.Util.SorryProof
import SciLean.Data.ColProd
import SciLean.Data.Idx

namespace SciLean

-- -- range given by the first and the last element(inclusive!)
-- def EnumType.Range (α : Type u) := Option (α × α)

class EnumType (ι : Type u) where

  decEq : DecidableEq ι
  
  -- Ther return type has `ForInStep` because it is useful to know if the loop 
  -- ended normall or if it was interupted. This way we can easily exit from nested loops
  forIn {m : Type v → Type w} [Monad m] {β : Type v} (init : β) (f : ι → β → m (ForInStep β)) : m (ForInStep β)

  -- something that foldM runs over all elements

  -- The slight issue is with ranges over `ι×κ` where we do not simply run
  -- from the first element to the last element but rather we run over all elements `(i,j)` 
  -- such that `i` is in the range and `j` is in the range
structure EnumType.FullRange (α : Type u)

def fullRange (ι) [EnumType ι] : EnumType.FullRange ι := EnumType.FullRange.mk

namespace EnumType 

  instance [inst : EnumType ι] : DecidableEq ι := inst.decEq


  private def _root_.ForInStep.value (b : ForInStep β) : β :=
    match b with
    | .done b => b
    | .yield b => b

  instance {ι} [EnumType ι] : ForIn m (FullRange ι) ι where
    forIn := λ _ init f => do pure (← forIn init f).value 

  instance : EnumType Empty :=
  {
    decEq := by infer_instance
    forIn := λ init _ => pure (.yield init)
  }
  
  instance : EnumType Unit :=
  {
    decEq := by infer_instance
    forIn := λ init f => f () init
  }

  @[inline] partial def Fin.forIn {m : Type → Type} [Monad m] {β : Type} (init : β) (f : Fin n → β → m (ForInStep β)) := do
      -- Here we use `StateT Bool m β` instead of `m (ForInStep β)` as compiler 
      -- seems to have much better time optimizing code with `StateT`
      let rec @[specialize] forLoop (i : Nat) (b : β) : StateT Bool m β := do
        if h : i < n then
          match (← f ⟨i,h⟩ b) with
          | ForInStep.done b  => set true; pure b
          | ForInStep.yield b => forLoop (i + 1) b
        else
          pure b
      let (val,b) ← forLoop 0 init false
      if b then
        return (ForInStep.done val)
      else
        return (ForInStep.yield val)

  @[inline] 
  instance : EnumType (Fin n) :=
  {
    decEq := by infer_instance
    forIn := Fin.forIn
  }

  @[inline]
  partial def Idx.forIn {m : Type → Type} [Monad m] {β : Type} (init : β) (f : Idx n → β → m (ForInStep β)) := do
      -- Here we use `StateT Bool m β` instead of `m (ForInStep β)` as compiler 
      -- seems to have much better time optimizing code with `StateT`
      let rec @[specialize] forLoop (i : USize) (b : β) : StateT Bool m β := do
        if h : i < n then
          match (← f ⟨i,h⟩ b) with
          | ForInStep.done b  => set true; pure b
          | ForInStep.yield b => forLoop (i + 1) b
        else
          pure b
      let (val,b) ← forLoop 0 init false
      if b then
        return (ForInStep.done val)
      else
        return (ForInStep.yield val)

  @[inline]
  partial instance : EnumType (Idx n) :=
  {
    decEq := by infer_instance

    forIn := Idx.forIn
  }

  @[inline]
  partial def Idx'.forIn {m : Type → Type} [Monad m] {β : Type} (init : β) (f : Idx' a b → β → m (ForInStep β)) := do
      -- Here we use `StateT Bool m β` instead of `m (ForInStep β)` as compiler 
      -- seems to have much better time optimizing code with `StateT`
      let rec @[specialize] forLoop (i : Int64) (val : β) : StateT Bool m β := do
        if _h : i ≤ b then
          match (← f ⟨i,sorry_proof⟩ val) with
          | ForInStep.done val  => set true; pure val
          | ForInStep.yield val => forLoop (i + 1) val
        else
          pure val
      let (val,b) ← forLoop a init false
      if b then
        return (ForInStep.done val)
      else
        return (ForInStep.yield val)


  @[inline]
  partial instance : EnumType (Idx' a b) :=
  {
    decEq := by infer_instance

    forIn := Idx'.forIn
  }


  -- /-- Embeds `ForInStep β` to `FoInStep (ForInStep β)`, useful for exiting from double for loops.
  -- -/
  -- @[inline] 
  -- private def forInStepDouble {m} [Monad m] {β : Type u} (x : m (ForInStep β)) 
  --   : m (ForInStep (ForInStep β)) := do
  --   match (← x) with
  --   | .done x => return .done (.done x)
  --   | .yield x => return .yield (.yield x)


  instance [EnumType ι] [EnumType κ]
           : EnumType (ι × κ) :=
  {
    decEq := by infer_instance

    forIn := λ {m} _ {β} init f => 
      EnumType.forIn (init:=init) λ (i : ι) (b : β) => 
        EnumType.forIn (init:=b) λ (j : κ) (b' : β) => f (i,j) b'
  }

  instance [EnumType ι] [EnumType κ]
           : EnumType (ι ×ₗ κ) :=
  {
    decEq := by infer_instance

    forIn := λ {m} _ {β} init f => 
      EnumType.forIn (init:=init) λ (j : κ) (b : β) => 
        EnumType.forIn (init:=b) λ (i : ι) (b' : β) => f (i,j) b'
  }


  instance [EnumType ι] [EnumType κ]
           : EnumType (ι ⊕ κ) :=
  {
    decEq := by infer_instance

    forIn := λ {m} _ {β} init f => do
      let b ← EnumType.forIn (init:=init) λ i b => f (.inl i) b

      match b with
      | .done b => pure (.done b)
      | .yield b => EnumType.forIn (init:=b) λ j b => f (.inr j) b
  }

  @[specialize] def sum {α} [Zero α] [Add α] {ι} [EnumType ι] (f : ι → α) : α := Id.run do
    (← EnumType.forIn (0 : α) λ (i : ι) a => .yield (a + f i)).value

  open Lean.TSyntax.Compat in
  macro " ∑ " xs:Lean.explicitBinders ", " b:term:66 : term => Lean.expandExplicitBinders ``EnumType.sum xs b

  @[app_unexpander sum] def unexpandSum : Lean.PrettyPrinter.Unexpander
    | `($(_) fun $x:ident => $b) => 
      `(∑ $x:ident, $b)
    | `($(_) fun $x:ident $xs:ident* => $b) => 
      `(∑ $x:ident, fun $xs* => $b)
    | `($(_) fun ($x:ident : $ty:term) => $b) => 
      `(∑ ($x:ident : $ty), $b)
    | _  => throw ()


  @[specialize] def product {α} [One α] [Mul α] {ι} [EnumType ι] (f : ι → α) : α := Id.run do
    (← EnumType.forIn (1 : α) λ (i : ι) a => .yield (a * f i)).value

  open Lean.TSyntax.Compat in
  macro " ∏ " xs:Lean.explicitBinders ", " b:term:66 : term => Lean.expandExplicitBinders ``product xs b

  @[app_unexpander product] def unexpandProduct : Lean.PrettyPrinter.Unexpander
    | `($(_) fun $x:ident => $b) => 
      `(∏ $x:ident, $b)
    | `($(_) fun $x:ident $xs:ident* => $b) => 
      `(∏ $x:ident, fun $xs* => $b)
    | `($(_) fun ($x:ident : $ty:term) => $b) => 
      `(∏ ($x:ident : $ty), $b)
    | _  => throw ()



  -- instance {ι} [EnumType ι] : Fintype ι where
  --   elems := {
  --       val := Id.run do
  --         let mut l : List ι := []
  --         for i in fullRange ι do
  --           l := i :: l
  --         Multiset.ofList l.reverse
  --       nodup := sorry_proof
  --     }
  --   complete := sorry_proof

  
  -- TODO: move this somewhere else
  -- namespace Tests

  -- def r1 : Range (Fin 125) := some (5,10)

  -- #eval for i in r1 do IO.println i
  -- #eval EnumType.foldM r1 (init := ()) λ _ i => IO.println i


  -- def r2 : Range (Idx 15) := some (⟨4, by native_decide⟩, ⟨10, by native_decide⟩)

  -- #eval for i in r2 do IO.println i
  -- #eval EnumType.foldM r2 (init := ()) λ _ i => IO.println i


  -- def r3 : Range (Idx 15 × Fin 10 × Fin 20) := some ((⟨0,sorry⟩, 3, 0), (⟨3,sorry⟩, 6, 2))

  -- #eval for (i,j,k) in r3 do
  --        IO.println (i,j,k)
  --        if i.1 == 2 && j.1 == 5 then
  --          break

  -- #eval EnumType.foldM r3 (init := ()) λ _ i => IO.println i



  -- def r4 : Range (Idx 15 ×ₗ Fin 10 × Fin 20) := some ((⟨0,sorry⟩, 3, 0), (⟨3,sorry⟩, 6, 2))

  -- #eval for (i,j,k) in r4 do
  --        IO.println (i,j,k)
  --        if i.1 == 2 && j.1 == 5 then
  --          break

  -- #eval EnumType.foldM r4 (init := ()) λ _ i => IO.println i


  -- def r5 : Range (Idx 15 ×ₗ (Fin 3 ⊕ Fin 4)) := some ((⟨0,sorry⟩, .inr 1), (⟨3,sorry⟩, .inr 2))

  -- #eval for (i,j) in r5 do
  --         if j == (Sum.inl 2) then
  --            IO.println "break"
  --            break
  --         IO.println (i,j)

  -- #eval EnumType.foldM r5 (init := ()) λ _ i => IO.println i


  -- end Tests

end EnumType
