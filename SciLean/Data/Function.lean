import Mathlib.Logic.Function.Basic
import SciLean.Data.Index

def Function.Inverse (g : β → α) (f : α → β) :=
  Function.LeftInverse g f ∧ Function.RightInverse g f

open SciLean

variable {α β}
  {ι} [EnumType ι]

def Function.foldlM {m} [Monad m] (f : ι → α) (op : β → α → m β) (init : β) : m β := do
  let mut b := init
  for i in fullRange ι do
    b ← op b (f i)
  return b

def Function.foldl (f : ι → α) (op : β → α → β) (init : β) : β :=
  Id.run <| Function.foldlM f (fun x y => pure (op x y)) init

variable [Index ι]

/--
  TODO: needs beter implementation but that requires refining EnumType and Index
  -/
def Function.reduceMD {m} [Monad m] (f : ι → α) (op : α → α → m α) (default : α) : m α := do
  let n := Index.size ι
  if n = 0 then
    return default
  let mut a := f (fromIdx ⟨0,sorry_proof⟩)
  for i in [1:n.toNat] do
    a ← op a (f (fromIdx ⟨i.toUSize,sorry_proof⟩))
  return a

def Function.reduceD (f : ι → α) (op : α → α → α) (default : α) : α :=
  let n := Index.size ι
  if n = 0 then
    default
  else 
    let a := f (fromIdx ⟨0,sorry_proof⟩)
    Function.foldl 
      (fun i : Idx (n-1) => 
        let i : Idx n := ⟨i.1+1, sorry_proof⟩
        let i : ι := fromIdx i
        f i)
      op
      a

abbrev Function.reduce [Inhabited α] (f : ι → α) (op : α → α → α) : α := 
  f.reduceD op default


section FunctionModify

variable {α : Sort u} {β : α → Sort v} {α' : Sort w} [DecidableEq α] [DecidableEq α']

/-- Similar to `Function.update` but `g` specifies how to change the value at `a'`. -/
def Function.modify (f : ∀ a, β a) (a' : α) (g : β a' → β a') (a : α) : β a := 
  Function.update f a' (g (f a')) a

@[simp]
theorem Function.modify_same (a : α) (g : β a → β a) (f : ∀ a, β a) : modify f a g a = g (f a) :=
  dif_pos rfl

@[simp]
theorem Function.modify_noteq {a a' : α} (h : a ≠ a') (g : β a' → β a') (f : ∀ a, β a) : modify f a' g a = f a :=
  dif_neg h

end FunctionModify


def Function.repeatIdx (f : ι → α → α) (init : α) : α := Id.run do
  let mut x := init
  for i in fullRange ι do
    x := f i x
  x

def Function.repeat (n : Nat) (f : α → α) (init : α) : α := 
  repeatIdx (fun (_ : Fin n) x => f x) init


@[simp]
theorem Function.repeatIdx_update {α : Type _} (f : ι → α → α) (g : ι → α)
  : repeatIdx (fun i g' => Function.update g' i (f i (g' i))) g
    =
    fun i => f i (g i) := sorry_proof

/-- Specialized formulation of `Function.repeatIdx_update` which is sometimes more 
succesfull with unification -/
@[simp]
theorem Function.repeatIdx_update' {α : Type _} (f : ι → α) (g : ι → α) (op : α → α → α)
  : repeatIdx (fun i g' => Function.update g' i (op (g' i) (f i))) g
    =
    fun i => op (g i) (f i) := 
by
  apply Function.repeatIdx_update (f := fun i x => op x (f i))
