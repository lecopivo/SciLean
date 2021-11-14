namespace SciLean

@[reducible]
def id : α → α := λ a => a

@[reducible]
def curry : (α × β → γ) → (α → β → γ) := λ f a b => f (a,b) 

@[reducible]
def uncurry : (α → β → γ) → (α × β → γ) := λ f ab => f ab.1 ab.2

@[reducible]
def eval {α} {β : α → Sort v} : (a : α) → ((a' : α) → (β a')) → (β a) := λ a f => f a

@[reducible]
def const : α → β → α := λ a b => a

@[reducible]
def swap : (α → β → γ) → (β → α → γ) := λ f b a => f a b

@[reducible]
def comp : (β → γ) → (α → β) → (α → γ) := Function.comp

@[reducible]
def fmap {E : α → Sort u} {F : α → Sort v} (f : (a : α) → E a → F a) 
    : ((a : α) → E a) → ((a' : α) → F a') := λ g a => (f a) (g a)

@[reducible]
def pmap : (α → γ) → (β → δ) → (α×β → γ×δ) := λ f g ac => (f ac.1, g ac.2)
