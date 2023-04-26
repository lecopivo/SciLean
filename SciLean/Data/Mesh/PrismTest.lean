import SciLean.Data.Mesh.Prism

namespace SciLean
open Prism

#check Face

/-- Embeds `ForInStep β` to `FoInStep (ForInStep β)`, useful for exiting from double for loops.
-/
@[inline] 
private def forInStepDouble {m} [Monad m] {β : Type u} (x : m (ForInStep β)) 
  : m (ForInStep (ForInStep β)) := do
  match (← x) with
  | .done x => return .done (.done x)
  | .yield x => return .yield (.yield x)



def _root_.ForInStep.andThen {m} [Monad m] (b : ForInStep β) (f : β → m (ForInStep β)) : m (ForInStep β) :=
  match b with
  | .done b => pure (.done b)
  | .yield b => f b

def _root_.ForInStep.value (b : ForInStep β) : β :=
  match b with
  | .done b => b
  | .yield b => b

local instance : Add (Option Nat) := ⟨λ n m => match n, m with | some n, some m => n+m | _, _ => none⟩

def Face.forIn {m} [Monad m] (P : Prism) (n : Nat) (init : β) (f : Face P n → β → m (ForInStep β)) : m (ForInStep β) := do
  match P, n with
  | ⟨.point, _⟩, 0 => f ⟨.point, sorry_proof, sorry_proof⟩ init
  | ⟨.point, _⟩, n+1 => pure (.yield init)
  | ⟨.cone P', _⟩, 0 => do
      let P' : Prism := ⟨P', sorry_proof⟩

      let b ← Face.forIn P' 0 init (λ q b => (f q.base b))
      let b ← b.andThen λ b => f (Face.tip P') b
      return b

  | ⟨.cone P', _⟩, n+1 => do
      let b ← Face.forIn ⟨P', sorry_proof⟩ (n+1) init (λ q b => (f q.base b))

      match b with
      | .done b => return .done b
      | .yield b => 
        Face.forIn ⟨P', sorry_proof⟩ n b (λ q b => (f q.cone b))

  | ⟨.prod P Q, _⟩, n => do
      let P : Prism := ⟨P, sorry_proof⟩
      let Q : Prism := ⟨Q, sorry_proof⟩
      
      let mut b := ForInStep.yield init

      for i in [0:n+1] do
        let j := n - i
        
        b ← Face.forIn Q j b.value λ q b =>
               Face.forIn P i b λ p b => 
                 f ⟨p.repr.prod q.repr, sorry_proof, sorry_proof⟩ b

        if let .done b' := b then
          return .done b'

      pure b


instance (n : Nat) : EnumType (Face P n) where
  decEq := by infer_instance
  forIn := λ init f => do pure (← Face.forIn P n init f).value

-- run over all dimensions and basic prisms
#eval show Lean.CoreM Unit from do

  let P := Prism.cube
  let dim := 1
  let mut i := 0

  for e in fullRange (Face P (some dim)) do
    if e.toFin.1 ≠ i then
      throwError "Mismatch between forIn interation `{i}` and index `{e.toFin}` on face {e.repr.toString} for prism {P.repr.toString}"

    IO.println s!"edge: {e.repr.toString} | id: {e.toFin}"

    i := i + 1


def Inclusion.forIn {m} [Monad m] (P : Prism) (Q : Prism) (init : β) (f : Inclusion Q P → β → m (ForInStep β)) : m (ForInStep β) := do
  match P, Q with
  | ⟨.point, _⟩, ⟨.point, _⟩ => f ⟨.point, sorry_proof, sorry_proof⟩ init
  | ⟨.point, _⟩, _ => pure (.yield init)
  | ⟨.cone P', _⟩, ⟨.point, _⟩ => do
      let P' : Prism := ⟨P', sorry_proof⟩

      let b ←
        Inclusion.forIn P' point init (λ q b => 
          let q : Inclusion _ _ := ⟨q.repr.base, sorry_proof, sorry_proof⟩
          f q b)

      let b ← b.andThen λ b => 
        let q : Inclusion _ _ := ⟨.tip P'.repr, sorry_proof, sorry_proof⟩
        f q b

      pure b

  | ⟨.cone P', _⟩, ⟨.cone Q', _⟩ => do
      let P' : Prism := ⟨P', sorry_proof⟩
      let Q' : Prism := ⟨Q', sorry_proof⟩

      let b ← 
        Inclusion.forIn P' Q'.cone init (λ q b => 
          let q : Inclusion _ _ := ⟨q.repr.base, sorry_proof, sorry_proof⟩
          (f q b))

      if let .done b := b then
        return .done b

      let b ← 
        Inclusion.forIn P' Q' b.value (λ q b => 
          let q : Inclusion _ _ := ⟨q.repr.cone, sorry_proof, sorry_proof⟩
          (f q b))

      pure b

  | ⟨.cone P', _⟩, ⟨.prod Q₁ Q₂, _⟩ => do
      let P' : Prism := ⟨P', sorry_proof⟩

      let b ← 
        Inclusion.forIn P' Q init (λ q b => 
          let q : Inclusion _ _ := ⟨q.repr.base, sorry_proof, sorry_proof⟩
          f q b)

      pure b

  | ⟨.prod P₁ P₂, _⟩, _ => do
      let P₁ : Prism := ⟨P₁, sorry_proof⟩
      let P₂ : Prism := ⟨P₂, sorry_proof⟩

      let mut b := ForInStep.yield init

      for dec in fullRange (PrismDecomposition Q) do

        let Q₁ := dec.fst
        let Q₂ := dec.snd

        b ← 
          Inclusion.forIn P₂ Q₂ init λ q₂ b => 
            Inclusion.forIn P₁ Q₁ b λ q₁ b => 
              f ⟨q₁.repr.prod q₂.repr, sorry_proof, sorry_proof⟩ b

        if let .done b' := b then
          return .done b'

      return b

instance {Q P : Prism} : EnumType (Inclusion Q P) where
  decEq := by infer_instance
  forIn := λ init f => do pure (← Inclusion.forIn P Q init f).value

-- run over all dimensions and basic prisms
#eval show Lean.CoreM Unit from do

  let P := Prism.square
  let Q := Prism.segment
  let mut i : Nat := 0

  for e in fullRange (Inclusion Q P) do
    IO.println s!"face: {e.repr.toString} | id: {i} | dim: {e.repr.toPrism.toCanonical.toString}"
    i := i + 1

  

-- def testFaceIterable (P : Prism) : IO Unit := do

--   for fDim in [0:P.dim+1] do

--     for face in 
