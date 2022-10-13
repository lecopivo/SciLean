import SciLean.Core

namespace SciLean


/-- Calls `(f (n+m-1) ∘ ...  ∘ f m) x`

Reverse composition is `funRevRec`
-/
def funRec {α : Nat → Type} (n m : Nat) (f : (n : Nat) → α n → α (n + 1)) (x : α m) : α (n + m) :=
  match n with
  | 0 => cast sorry_proof x
  | n + 1 => f (n+m) (cast sorry_proof (funRec n m f x)) |> (cast sorry_proof ·)

instance {α : Nat → Type} [∀ n, Vec (α n)] 
  (f : (n : Nat) → α n → α (n + 1)) [∀ n, IsLin (f n)] (n : Nat) 
  : IsLin (funRec n m f) := sorry_proof

instance {α : Nat → Type} [∀ n, Vec (α n)] 
  (f : (n : Nat) → α n → α (n + 1)) [∀ n, IsSmooth (f n)] (n : Nat) 
  : IsSmooth (funRec n m f) := sorry_proof

instance {α : Nat → Type} [∀ n, SemiHilbert (α n)] 
  (f : (n : Nat) → α n → α (n + 1)) [∀ n, IsSmooth (f n)] (n : Nat) 
  : HasAdjoint (funRec n m f) := sorry_proof

/-- Calls `(f m ∘ ...  ∘ f (n+m-1)) x`

Reverse composition is `funRec`
-/
def funRevRec {α : Nat → Type} (n m : Nat) (f : (n' : Nat) → α (n' + 1) → α n') (x : α (n + m)) : α m :=
  match n with
  | 0 => cast sorry_proof x
  | n' + 1 => 
    funRevRec n' m f (f (n'+m) (cast sorry_proof x))

instance funRevRec.arg_x.isLin {α : Nat → Type} [∀ n, Vec (α n)] 
  (f : (n : Nat) → α (n + 1) → α n) [∀ n, IsLin (f n)] (n m : Nat)
  : IsLin (funRevRec n m f) := sorry_proof

instance {α : Nat → Type} [∀ n, Vec (α n)] 
  (f : (n : Nat) → α (n + 1) → α n) [∀ n, IsSmooth (f n)] (n m : Nat)
  : IsSmooth (funRevRec n m f) := sorry_proof

instance {X} {α : Nat → Type} [∀ n, Vec (α n)] [Vec X]
  (f : (x : X) → (n : Nat) → α (n + 1) → α n) [∀ n, IsSmooth (λ x => f x n)] [∀ x n, IsSmooth (f n x)] (n m : Nat)
  : IsSmooth (λ x => funRevRec n m (f x)) := sorry_proof

instance funRevRec.arg_x.hasAdjoint {α : Nat → Type} [∀ n, SemiHilbert (α n)] 
  (f : (n : Nat) → α (n + 1) → α n) [∀ n, HasAdjoint (f n)] (n m : Nat)
  : HasAdjoint (funRevRec n m f) := sorry_proof

@[simp]
theorem funRevRec.arg_x.adj_simp {α : Nat → Type} [∀ n, SemiHilbert (α n)] 
  (f : (n : Nat) → α (n + 1) → α n) [∀ n, HasAdjoint (f n)] (n m : Nat)
  : (λ x => funRevRec n m f x)† = (λ x' => funRec n m (λ n => (f n)†) x') := sorry_proof

