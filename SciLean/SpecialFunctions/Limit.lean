module

@[expose] public section

namespace SciLean

def has_limit {X} (lim : Nat → X) : Prop := sorry

noncomputable
def limit {X} (lim : Nat → X) : X := sorry

def Filter (α : Type) : Type := sorry
def neighbourhood (a : α) : Filter α := sorry

prefix:max "𝓝" => neighbourhood

noncomputable
def lim {α β} (filter : Filter α) (f : α → β) : β := sorry
