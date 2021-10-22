namespace SciLean

@[reducible]
def curry : (α×β → γ) → (α → β → γ) := λ f a b => f (a,b) 

@[reducible]
def uncurry : (α → β → γ) → (α×β → γ) := λ f (a,b) => f a b

@[reducible]
def eval {α} {β : α → Sort v} : (a : α) → ((a' : α) → (β a')) → (β a) := λ a f => f a

@[reducible]
def const : α → β → α := λ a b => a

@[reducible]
def comp : (β → γ) → (α → β) → (α → γ) := λ f g a => f (g a)

@[reducible]
def fmap {E : α → Sort u} {F : α → Sort v} (f : (a : α) → E a → F a) 
    : ((a : α) → E a) → ((a : α) → F a) := λ g a => (f a) (g a)
