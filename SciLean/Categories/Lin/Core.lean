import SciLean.Categories.Lin.Basic

namespace SciLean.Lin

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

-- id
instance : IsLin (id : X → X) := sorry
instance : IsLin (λ x : X => x) := sorry

-- constant
instance : IsLin (λ (x : X) (b : β) => x) := sorry
instance : IsLin (λ (y : Y) => (0 : X)) := sorry

-- swaping arguments
instance : IsLin (λ (f : α → β → Z) (b : β) (a : α) => f a b) := sorry
instance (f : α → Y → Z) [∀ a, IsLin (f a)] : IsLin (λ (y : Y) (a : α) => f a y) := sorry
instance (f : X → β → Z) (b : β) [IsLin f] : IsLin (λ (x : X) => f x b) := sorry

----------------
-- evaluation --
----------------
instance : IsLin (λ (f : α → Y) (a : α) => f a) := sorry
-- instance (f : Y → Z) [IsLin f] : IsLin (λ (g : α → Y) (a : α) => f (g a)) := sorry

-----------------
-- compitision --
-----------------
section composition

  variable (g : X → Y) [IsLin g] 

  instance (f : Y → Z) [IsLin f] 
           : IsLin (λ x => f (g x)) := sorry

  -- one extra arg
  instance (f : Y → α → Z) (a : α) [IsLin (λ y => f y a)] 
           : IsLin (λ x => f (g x) a) := sorry

  -- two extra arg
  instance (f : Y → α → β → Z) (a : α) (b : β) [IsLin (λ y => f y a b)] 
           : IsLin (λ x => f (g x) a b) := sorry

  -- three extra arg
  instance (f : Y → α → β → γ → Z) (a : α) (b : β) (c : γ) [IsLin (λ y => f y a b c)] 
           : IsLin (λ x => f (g x) a b c) := sorry

  -- four extra args
  -- .
  -- .
  -- .

end composition

--------------
-- diagonal --
--------------
section diagonal

  variable (g : W → X) [IsLin g] 
  variable (h : W → Y) [IsLin h]

  instance (f : X → Y → Z) [IsLin (λ p : X×Y => f p.1 p.2)] 
           : IsLin (λ w => f (g w) (h w)) := sorry

  -- one extra arg
  instance (f : X → α → Y → Z) (a : α) [IsLin (λ p : X × Y => f p.1 a p.2)]
           : IsLin (λ w => f (g w) a (h w)) := sorry
  instance (f : X → Y → α → Z) (a : α) [IsLin (λ p : X × Y => f p.1 p.2 a)]
           : IsLin (λ w => f (g w) (h w) a) := sorry

  -- two extra arg
  instance (f : X → α → β → Y → Z) (a : α) (b : β) [IsLin (λ p : X × Y => f p.1 a b p.2)] 
           : IsLin (λ w => f (g w) a b (h w)) := sorry
  instance (f : X → α → Y → β → Z) (a : α) (b : β) [IsLin (λ p : X × Y => f p.1 a p.2 b)] 
           : IsLin (λ w => f (g w) a (h w) b) := sorry
  instance (f : X → Y → α → β → Z) (a : α) (b : β) [IsLin (λ p : X × Y => f p.1 p.2 a b)] 
           : IsLin (λ w => f (g w) (h w) a b) := sorry

  -- three extra args
  -- .
  -- .
  -- .

end diagonal

-----------------------
-- curry and uncurry --
-----------------------
section curry

  -- instance (f : X×Y → Z) [IsLin f] (y : Y) [IsZero y] : IsLin (λ x => f (x,y)) := sorry
  -- instance (f : X×Y → Z) [IsLin f] (x : X) [IsZero x] : IsLin (λ y => f (x,y)) := sorry

end curry
