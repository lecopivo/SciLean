import SciLean.Categories.Smooth.Basic

namespace SciLean.Smooth

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]


--- The order of these instance is important :( This should not be ... as it can cause problem

-- swaping arguments
instance : IsSmooth (λ (f : α → β → Z) (b : β) (a : α) => f a b) := sorry
instance (f : α → Y → Z) [∀ a, IsSmooth (f a)] : IsSmooth (λ (y : Y) (a : α) => f a y) := sorry  --- This one is dangerous :( and 
instance (f : X → β → Z) (b : β) [IsSmooth f] : IsSmooth (λ (x : X) => f x b) := sorry

--------------
-- diagonal --
--------------
section diagonal

  variable (g : W → X) 
  variable (h : W → Y) 

  instance (f : X → Y → Z) [IsSmooth (λ x y => f x y)] [∀ x, IsSmooth (λ y => f x y)] 
           [IsSmooth g] [IsSmooth h]
           : IsSmooth (λ w => f (g w) (h w)) := sorry

  -- one extra arg -- these cause some issues :( 
  instance (f : X → α → Y → Z) (a : α) [IsSmooth (λ x y => f x a y)] [∀ x, IsSmooth (λ y => f x a y)] 
           [IsSmooth g] [IsSmooth h]
           : IsSmooth (λ w => f (g w) a (h w)) := sorry
  instance (f : X → Y → α → Z) (a : α) [IsSmooth (λ x y => f x y a)] [∀ x, IsSmooth (λ y => f x y a)] 
           [IsSmooth g] [IsSmooth h]
           : IsSmooth (λ w => f (g w) (h w) a) := sorry

  -- two extra arg
  instance (f : X → α → β → Y → Z) (a : α) (b : β) [IsSmooth (λ x y => f x a b y)] [IsSmooth (λ y x => f x a b y)] 
           [IsSmooth g] [IsSmooth h]
           : IsSmooth (λ w => f (g w) a b (h w)) := sorry
  instance (f : X → α → Y → β → Z) (a : α) (b : β) [IsSmooth (λ x y => f x a y b)] [IsSmooth (λ y x => f x a y b)]
           [IsSmooth g] [IsSmooth h] 
           : IsSmooth (λ w => f (g w) a (h w) b) := sorry
  instance (f : X → Y → α → β → Z) (a : α) (b : β) [IsSmooth (λ x y => f x y a b)] [IsSmooth (λ y x => f x y a b)] 
           [IsSmooth g] [IsSmooth h]
           : IsSmooth (λ w => f (g w) (h w) a b) := sorry

  -- three extra args
  -- .
  -- .
  -- .

end diagonal 


-----------------
-- composition --
-----------------
section composition

  variable (g : X → Y)

  instance (f : Y → Z) [IsSmooth f] 
           [IsSmooth g] 
           : IsSmooth (λ x => f (g x)) := sorry

  -- one extra arg
  instance (f : Y → α → Z) (a : α) [IsSmooth (λ y => f y a)] 
           [IsSmooth g] 
           : IsSmooth (λ x => f (g x) a) := sorry

  -- two extra arg
  instance (f : Y → α → β → Z) (a : α) (b : β) [IsSmooth (λ y => f y a b)] 
           [IsSmooth g] 
           : IsSmooth (λ x => f (g x) a b) := sorry

  -- three extra arg
  instance (f : Y → α → β → γ → Z) (a : α) (b : β) (c : γ) [IsSmooth (λ y => f y a b c)] 
           [IsSmooth g] 
           : IsSmooth (λ x => f (g x) a b c) := sorry

  -- four extra args
  -- .
  -- .
  -- .

end composition


----------------
-- evaluation --
----------------
instance : IsSmooth (λ (f : α → Y) (a : α) => f a) := sorry
-- instance (f : Y → Z) [IsSmooth f] : IsSmooth (λ (g : α → Y) (a : α) => f (g a)) := sorry

-- constant
instance : IsSmooth (λ (x : X) (b : β) => x) := sorry
instance (x : X) : IsSmooth (λ (y : Y) => x) := sorry

-- id
instance : IsSmooth (id : X → X) := sorry
instance : IsSmooth (λ x : X => x) := sorry

-----------------------
-- curry and uncurry --
-----------------------
section curry

  instance (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)] : IsSmooth (λ xy : X×Y => f xy.1 xy.2) := sorry
  instance (f : X×Y → Z) [IsSmooth f] : IsSmooth (λ x y => f (x,y)) := sorry
  instance (f : X×Y → Z) [IsSmooth f] : IsSmooth (λ y x => f (x,y)) := sorry

end curry
