namespace SciLean

@[reducible]
def id : α → α := λ a => a
@[simp] theorem id_eval (a : α) : id a = a := by simp

@[reducible]
def curry : (α × β → γ) → (α → β → γ) := λ f a b => f (a,b) 
@[simp] theorem curry_eval (f : α × β → γ) (a : α) (b : β) : curry f a b = f (a,b) := by simp

@[reducible]
def uncurry : (α → β → γ) → (α × β → γ) := λ f ab => f ab.1 ab.2
@[simp] theorem uncurry_eval (f : α → β → γ) (ab : α × β) : uncurry f ab = f ab.1 ab.2 := by simp

@[reducible]
def eval {α} {β : α → Sort v} : (a : α) → ((a' : α) → (β a')) → (β a) := λ a f => f a

@[reducible]
def const : α → β → α := λ a b => a

@[reducible]
def swap : (α → β → γ) → (β → α → γ) := λ f b a => f a b

@[reducible]
def comp : (β → γ) → (α → β) → (α → γ) := Function.comp
@[simp] theorem comp_eval (f : β → γ) (g : α → β) (a : α) : comp f g a = f (g a) := by simp

@[reducible]
def fmap {E : α → Sort u} {F : α → Sort v} (f : (a : α) → E a → F a) 
    : ((a : α) → E a) → ((a' : α) → F a') := λ g a => (f a) (g a)

@[reducible]
def pmap : (α → γ) → (β → δ) → (α×β → γ×δ) := λ f g ac => (f ac.1, g ac.2)
@[simp] theorem pmap_eval (f : α → γ) (g : β → δ) (ab : α×β) : pmap f g ab = (f ab.1, g ab.2) := by simp
