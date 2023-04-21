import Mathlib.Algebra.Group.Defs
import SciLean.Mathlib.Data.ColProd
import SciLean.Data.Idx

namespace SciLean

-- range given by the first and the last element(inclusive!)
def EnumType.Range (α : Type u) := Option (α × α)

class EnumType (ι : Type u) where
  -- next  : ι → Option ι
  fullRange : EnumType.Range ι

  decEq : DecidableEq ι

  forIn {m : Type → Type} [Monad m] {β : Type} (range : EnumType.Range ι) (init : β) (f : ι → β → m (ForInStep β)) : m β
  foldM {m : Type → Type} [Monad m] {β : Type} (range : EnumType.Range ι) (f : β → ι → m β) (init : β) : m β :=
    forIn fullRange init (λ i b => f b i >>= pure ∘ .yield)

  -- foldM_forIn : ∀ {m} [Monad m] {β} r (f : β → ι → m β) init, 
  --   foldM r f init = forIn r init (λ i b => f b i >>= pure ∘ .yield)

  -- something that foldM runs over all elements

  -- The slight issue is with ranges over `ι×κ` where we do not simply run
  -- from the first element to the last element but rather we run over all elements `(i,j)` 
  -- such that `i` is in the range and `j` is in the range


def fullRange (ι) [EnumType ι] : EnumType.Range ι := EnumType.fullRange

namespace EnumType 

  instance [inst : EnumType ι] : DecidableEq ι := inst.decEq

  instance {ι} [EnumType ι] : ForIn m (Range ι) ι where
    forIn := forIn

  instance : EnumType Empty :=
  {
    fullRange := none
    decEq := by infer_instance
    foldM := λ _ _ init => pure init
    forIn := λ _ init _ => pure init
  }
  
  instance : EnumType Unit :=
  {
    fullRange := some ((),())
    decEq := by infer_instance
    foldM := λ range f init => if range.isSome then f init () else pure init
    forIn := λ range init f => 
      match range with 
      | some _ => do
        match (← f () init) with
        | .done b => pure b
        | .yield b => pure b
      | none => pure init
  }

  @[inline] partial def Fin.forIn {m : Type → Type} [Monad m] {β : Type} (range : EnumType.Range (Fin n)) (init : β) (f : Fin n → β → m (ForInStep β)) :=
      let rec @[specialize] forLoop (i : Fin n) (stop : Fin n) (b : β) : m β := do
        match (← f i b) with
        | ForInStep.done b  => pure b
        | ForInStep.yield b => 
          if i < stop then
            forLoop ⟨i.1 + 1, sorry⟩ stop b
          else
            pure b
      match range with
      | some (start, stop) => 
        if start ≤ stop then
          forLoop start stop init
        else
          pure init
      | none => pure init

  @[inline] partial def Fin.foldM {m : Type → Type} [Monad m] {β : Type} (range : EnumType.Range (Fin n)) (f : β → Fin n → m β) (init : β) :=
      let rec @[specialize] foldLoop (i : Fin n) (stop : Fin n) (b : β) : m β := do
        let b' ← f b i
        if i < stop then
          foldLoop ⟨i.1+1, sorry⟩ stop b'
        else
          pure b'
      match range with
      | some (start,stop) => 
        if start ≤ stop then 
          foldLoop start stop init 
        else 
          pure init
      | none => pure init


  @[inline] 
  def Fin.fullRange (n) : Range (Fin n):=       
      if h : 0 < n then
        some (⟨0,h⟩, ⟨n-1,sorry⟩)
      else
        none

  @[inline] 
  instance : EnumType (Fin n) :=
  {
    fullRange := Fin.fullRange n

    decEq := by infer_instance

    foldM := Fin.foldM
    forIn := Fin.forIn

  }

  @[inline]
  partial def Idx.forIn {m : Type → Type} [Monad m] {β : Type} (range : EnumType.Range (Idx n)) (init : β) (f : Idx n → β → m (ForInStep β)) :=
      let rec @[specialize] forLoop (i : Idx n) (stop : Idx n) (b : β) : m β := do
        match (← f i b) with
        | ForInStep.done b  => pure b
        | ForInStep.yield b => 
          if i < stop then
            forLoop ⟨i.1 + 1, sorry⟩ stop b
          else
            pure b
      match range with
      | some (start, stop) => 
        if start ≤ stop then
          forLoop start stop init
        else
          pure init
      | none => pure init


  @[inline] 
  partial def Idx.foldM {m : Type → Type} [Monad m] {β : Type} (range : EnumType.Range (Idx n)) (f : β → Idx n → m β) (init : β) :=
      let rec @[specialize] foldLoop (i : Idx n) (stop : Idx n) (b : β) : m β := do
        let b' ← f b i
        if i < stop then
          foldLoop ⟨i.1+1, sorry⟩ stop b'
        else
          pure b'
      match range with
      | some (start,stop) => 
        if start ≤ stop then 
          foldLoop start stop init 
        else 
          pure init
      | none => pure init

  @[inline] 
  partial def Idx.fold {β : Type} (range : EnumType.Range (Idx n)) (f : β → Idx n → β) (init : β) :=
      let rec @[specialize] foldLoop (i : Idx n) (stop : Idx n) (b : β) : β :=
        let b' := f b i
        if i < stop then
          foldLoop ⟨i.1+1, sorry⟩ stop b'
        else
          b'
      match range with
      | some (start,stop) => 
        if start ≤ stop then 
          foldLoop start stop init 
        else 
          init
      | none => init


  @[inline]
  def Idx.fullRange (n) : Range (Idx n) := 
      if h : 0 < n then
        some (⟨0,h⟩, ⟨n-1,sorry⟩)
      else
        none


  @[inline]
  partial instance : EnumType (Idx n) :=
  {
    fullRange := Idx.fullRange n
    decEq := by infer_instance

    foldM := Idx.foldM
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
    fullRange := 
      match fullRange (ι:=ι), fullRange (ι:=κ) with
      | some (ι₁, ι₂), some (κ₁, κ₂) => some ((ι₁,κ₁), (ι₂,κ₂))
      | _, _ => none

    decEq := by infer_instance

    foldM := λ r f init => 
      match r with
      | some ((ι₁,κ₁),(ι₂,κ₂)) =>
        EnumType.foldM (some (ι₁, ι₂)) (init:=init) λ a (i : ι) => 
          EnumType.foldM (some (κ₁, κ₂)) (init:=a) λ a' (j : κ) => 
            f a' (i,j)
      | none => pure init

    forIn := λ {m} _ {β} range init f => 
      match range with
      | none => pure init
      | some ((ι₁,κ₁),(ι₂,κ₂)) =>
        EnumType.forIn (some (ι₁,ι₂)) (init:=init) λ (i : ι) (b : β) => do
          EnumType.forIn (some (κ₁,κ₂)) (init:=.yield b) λ (j : κ) (b' : ForInStep β) => do
            match b' with
            | .done b' => return .done (.done b')
            | .yield b' => forInStepDouble (f (i,j) b') 
  }

  instance [EnumType ι] [EnumType κ]
           : EnumType (ι ×ₗ κ) :=
  {
    fullRange := 
      match fullRange (ι:=ι), fullRange (ι:=κ) with
      | some (ι₁, ι₂), some (κ₁, κ₂) => some ((ι₁,κ₁), (ι₂,κ₂))
      | _, _ => none

    decEq := by infer_instance

    foldM := λ r f init => 
      match r with
      | some ((ι₁,κ₁),(ι₂,κ₂)) =>
        EnumType.foldM (some (κ₁,κ₂)) (init:=init) λ a (j : κ) => 
          EnumType.foldM (some (ι₁, ι₂)) (init:=a) λ a' (i : ι) => 
            f a' (i,j)
      | none => pure init

    forIn := λ {m} _ {β} range init f => 
      match range with
      | none => pure init
      | some ((ι₁,κ₁),(ι₂,κ₂)) =>
        EnumType.forIn (some (κ₁,κ₂)) (init:=init) λ (j : κ) (b : β) => do
          EnumType.forIn (some (ι₁,ι₂)) (init:=.yield b) λ (i : ι) (b' : ForInStep β) => do
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
    fullRange := 
      match fullRange (ι:=ι), fullRange (ι:=κ) with
      | some (ι₁, ι₂), some (κ₁, κ₂) => some (.inl ι₁, .inr κ₂)
      | some (ι₁, ι₂), none => some (.inl ι₁, .inl ι₂)
      | none, some (κ₁, κ₂) => some (.inr κ₁, .inr κ₂)
      | _, _ => none

    decEq := by infer_instance

    foldM := λ r f init => 
      match r with
      | none => pure init
      | some (.inl ι₁,.inl ι₂) =>
        EnumType.foldM (some (ι₁,ι₂)) (init:=init) λ b i => f b (.inl i)
      | some (.inr κ₁, .inr κ₂) =>
        EnumType.foldM (some (κ₁,κ₂)) (init:=init) λ b j => f b (.inr j)
      | some (.inl ι₁, .inr κ₂) => do
        let b ← 
          match fullRange (ι:=ι) with
          | some (_, ι₂) => EnumType.foldM (some (ι₁,ι₂)) (init:=init) λ b (i : ι) => f b (.inl i)
          | none => pure init

        match fullRange (ι:=κ) with
        | some (κ₁, _) => EnumType.foldM (some (κ₁,κ₂)) (init:=b) λ b (j : κ) => f b (.inr j)
        | none => pure b
      | _ => pure init

    forIn := λ {m} _ {β} range init f => 
      match range with
      | none => pure init
      | some (.inl ι₁,.inl ι₂) =>
        EnumType.forIn (some (ι₁,ι₂)) (init:=init) λ i b => f (.inl i) b
      | some (.inr κ₁, .inr κ₂) =>
        EnumType.forIn (some (κ₁,κ₂)) (init:=init) λ j b => f (.inr j) b
      | some (.inl ι₁, .inr κ₂) => do
        let b : ForInStep β ←
          match (fullRange (ι:=ι)) with
          | some (_, ι₂) => 
            EnumType.forIn (some (ι₁,ι₂)) (init:=ForInStep.yield init) λ i b => 
              match b with
              | .done b' => return .done (.done b')
              | .yield b' => forInStepDouble (f (.inl i) b') 
          | none => pure (.yield init)

        match b, (fullRange (ι:=κ)) with
        | .done b, _ => pure b
        | .yield b, some (κ₁, _) => EnumType.forIn (some (κ₁,κ₂)) (init:=b) λ j b => f (.inr j) b
        | .yield b, none => pure b

      | _ => pure init

  }

  @[specialize] def sum {α} [Zero α] [Add α] {ι} [EnumType ι] (f : ι → α) : α := Id.run do
    EnumType.foldM EnumType.fullRange (init := (0 : α)) λ a i => a + f i


  open Lean.TSyntax.Compat in
  macro "∑" xs:Lean.explicitBinders ", " b:term:66 : term => Lean.expandExplicitBinders ``EnumType.sum xs b

  
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
