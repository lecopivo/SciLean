import Mathlib.Algebra.Group.Defs
import SciLean.Mathlib.Data.ColProd
import SciLean.Data.Idx

namespace SciLean

-- -- range given by the first and the last element(inclusive!)
-- def EnumType.Range (α : Type u) := Option (α × α)

class EnumType (ι : Type u) where

  decEq : DecidableEq ι
  
  forIn {m : Type → Type} [Monad m] {β : Type} (init : β) (f : ι → β → m (ForInStep β)) : m β

  -- something that foldM runs over all elements

  -- The slight issue is with ranges over `ι×κ` where we do not simply run
  -- from the first element to the last element but rather we run over all elements `(i,j)` 
  -- such that `i` is in the range and `j` is in the range
structure EnumType.FullRange (α : Type u)

def fullRange (ι) [EnumType ι] : EnumType.FullRange ι := EnumType.FullRange.mk

namespace EnumType 

  instance [inst : EnumType ι] : DecidableEq ι := inst.decEq

  instance {ι} [EnumType ι] : ForIn m (FullRange ι) ι where
    forIn := λ _ init f => forIn init f

  instance : EnumType Empty :=
  {
    decEq := by infer_instance
    forIn := λ init _ => pure init
  }
  
  instance : EnumType Unit :=
  {
    decEq := by infer_instance
    forIn := λ init f => do
      match (← f () init) with
      | .done b => pure b
      | .yield b => pure b
  }

  @[inline] partial def Fin.forIn {m : Type → Type} [Monad m] {β : Type} (init : β) (f : Fin n → β → m (ForInStep β)) :=
      let rec @[specialize] forLoop (i : Nat) (b : β) : m β := do
        if h : i < n then
          match (← f ⟨i,h⟩ b) with
          | ForInStep.done b  => pure b
          | ForInStep.yield b => forLoop (i + 1) b
        else
          pure b
      if 0 < n then
        forLoop 0 init
      else
        pure init

  @[inline] 
  instance : EnumType (Fin n) :=
  {
    decEq := by infer_instance
    forIn := Fin.forIn
  }

  @[inline]
  partial def Idx.forIn {m : Type → Type} [Monad m] {β : Type} (init : β) (f : Idx n → β → m (ForInStep β)) :=
      let rec @[specialize] forLoop (i : USize) (b : β) : m β := do
        if h : i < n then
          match (← f ⟨i,h⟩ b) with
          | ForInStep.done b  => pure b
          | ForInStep.yield b => forLoop (i + 1) b
        else
          pure b
      if 0 < n then
        forLoop 0 init
      else
        pure init

  @[inline]
  partial instance : EnumType (Idx n) :=
  {
    decEq := by infer_instance

    forIn := Idx.forIn
  }


  /-- Embeds `ForInStep β` to `FoInStep (ForInStep β)`, useful for exiting from double for loops.
  -/
  @[inline] 
  private def forInStepDouble {m} [Monad m] {β : Type u} (x : m (ForInStep β)) 
    : m (ForInStep (ForInStep β)) := do
    match (← x) with
    | .done x => return .done (.done x)
    | .yield x => return .yield (.yield x)


  instance [EnumType ι] [EnumType κ]
           : EnumType (ι × κ) :=
  {
    decEq := by infer_instance

    forIn := λ {m} _ {β} init f => 
      EnumType.forIn  (init:=init) λ (i : ι) (b : β) => do
        EnumType.forIn (init:=.yield b) λ (j : κ) (b' : ForInStep β) => do
          match b' with
          | .done b' => return .done (.done b')
          | .yield b' => forInStepDouble (f (i,j) b') 
  }

  instance [EnumType ι] [EnumType κ]
           : EnumType (ι ×ₗ κ) :=
  {
    decEq := by infer_instance

    forIn := λ {m} _ {β} init f => 
      EnumType.forIn (init:=init) λ (j : κ) (b : β) => do
        EnumType.forIn (init:=.yield b) λ (i : ι) (b' : ForInStep β) => do
          match b' with
          | .done b' => return .done (.done b')
          | .yield b' => 
            match (← f (i,j) b') with
            | .done b'' => return .done (.done b'')
            | .yield b'' => return .yield (.yield b'')      
  }


  instance [EnumType ι] [EnumType κ]
           : EnumType (ι ⊕ κ) :=
  {
    decEq := by infer_instance

    forIn := λ {m} _ {β} init f => do
      let b : ForInStep β ←
          EnumType.forIn (init:=ForInStep.yield init) λ i b => 
            match b with
            | .done b' => return .done (.done b')
            | .yield b' => forInStepDouble (f (.inl i) b') 

      match b with
      | .done b => pure b
      | .yield b => EnumType.forIn (init:=b) λ j b => f (.inr j) b

  }

  @[specialize] def sum {α} [Zero α] [Add α] {ι} [EnumType ι] (f : ι → α) : α := Id.run do
    EnumType.forIn (0 : α) λ (i : ι) a => .yield (a + f i) -- λ a i => a + f i

  open Lean.TSyntax.Compat in
  macro "∑" xs:Lean.explicitBinders ", " b:term:66 : term => Lean.expandExplicitBinders ``EnumType.sum xs b

  @[specialize] def product {α} [One α] [Mul α] {ι} [EnumType ι] (f : ι → α) : α := Id.run do
    EnumType.forIn (1 : α) λ (i : ι) a => .yield (a * f i)

  open Lean.TSyntax.Compat in
  macro "∏" xs:Lean.explicitBinders ", " b:term:66 : term => Lean.expandExplicitBinders ``product xs b


  
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
