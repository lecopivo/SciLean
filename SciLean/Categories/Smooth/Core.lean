import SciLean.Categories.Core
import SciLean.Categories.Smooth.Basic

namespace SciLean.Smooth

variable {b : Bool}
variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]


--- The order of these instance is important :( This should not be ... as it can cause problem

-- swaping arguments
-- instance : IsSmooth (λ (f : α → β → Z) (b : β) (a : α) => f a b) := sorry

-- Can I live without this one? 

-- instance (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
--          (g : X → Y) [IsSmooth g]
--          : IsSmooth (λ x => f x (g x)) := sorry

-- instance (f : α → Y → Z) [∀ a, IsSmooth (f a)] : IsSmooth (λ (y : Y) (a : α) => f a y) := sorry -- I want this one, but it is dangerous :(

instance (f : X → β → Z) (b : β) [IsSmooth f] : IsSmooth (λ (x : X) => f x b) := sorry
instance (f : X → β → γ → Z) (b : β) [IsSmooth f] : IsSmooth (λ (x : X) (c : γ) => f x b c) := sorry


-- instance (f : X → β → Z) (b : β) [IsSmooth f] : IsSmooth (swap f b) := by simp[swap]; infer_instance; done
-- instance (f : α → Y → Z) [IsSmooth (swap f)] : IsSmooth (λ (y : Y) (a : α) => f a y) := sorry

-- instance (f : α → β → Y → Z) [∀ a b, IsSmooth (f a b) (flag := true)] : IsSmooth (λ (y : Y) (a : α) (b : β) => f a b y) := sorry
-- instance (f : α → β → γ → Y → Z) [∀ a b c, IsSmooth (f a b c) (flag := true)] : IsSmooth (λ (y : Y) (a : α) (b : β) (c : γ) => f a b c y) := sorry


-- instance (f : α → Y → Z) (a : α) [IsSmooth (f a)] : IsSmooth (f a) (flag := true):= sorry


--- These two are dangerous - can cause infinit loop :(




--------------
-- diagonal --
--------------
-- section diagonal

  variable (g : W → X) 
  variable (h : W → Y) 

  instance (f : X → Y → Z) [IsSmooth f] [IsSmooth (swap f)] 
           [IsSmooth g] [IsSmooth h]
           : IsSmooth (λ w => f (g w) (h w)) := sorry

  -- one extra arg -- these cause some issues :( 
  -- instance (f : X → α → Y → Z) (a : α) [IsSmooth (λ x y => f x a y)] [IsSmooth (λ y x => f x a y)] 
  --          [IsSmooth g] [IsSmooth h]
  --          : IsSmooth (λ w => f (g w) a (h w)) := sorry
  -- instance (f : X → Y → α → Z) (a : α) [IsSmooth (λ x y => f x y a)] [IsSmooth (λ y x => f x y a)] 
  --          [IsSmooth g] [IsSmooth h]
  --          : IsSmooth (λ w => f (g w) (h w) a) := sorry

  -- -- two extra arg
  -- instance (f : X → α → β → Y → Z) (a : α) (b : β) [IsSmooth (λ x y => f x a b y)] [IsSmooth (λ y x => f x a b y)] 
  --          [IsSmooth g] [IsSmooth h]
  --          : IsSmooth (λ w => f (g w) a b (h w)) := sorry
  -- instance (f : X → α → Y → β → Z) (a : α) (b : β) [IsSmooth (λ x y => f x a y b)] [IsSmooth (λ y x => f x a y b)]
  --          [IsSmooth g] [IsSmooth h] 
  --          : IsSmooth (λ w => f (g w) a (h w) b) := sorry
  -- instance (f : X → Y → α → β → Z) (a : α) (b : β) [IsSmooth (λ x y => f x y a b)] [IsSmooth (λ y x => f x y a b)] 
  --          [IsSmooth g] [IsSmooth h]
  --          : IsSmooth (λ w => f (g w) (h w) a b) := sorry

--   -- three extra args
--   -- .
--   -- .
--   -- .

-- end diagonal 


------------------
-- Substitution --
------------------
section substitution
  

  -- instance (f : X → X → Y) [IsSmooth f] [IsSmooth (swap f)]
  --          : IsSmooth (λ x => f x x) := sorry



end substitution


-----------------
-- composition --
-----------------
section composition

  variable {A0 A1 A2 A3 A4 A5 A6 : Type}
  variable {X0 X1 X2 X3 X4 X5 X6 : Type} [Vec X0] [Vec X1] [Vec X2] [Vec X3] [Vec X4] [Vec X5] [Vec X6]

  variable (f1 : X1 → X2) [IsSmooth f1]
  variable (f2 : X2 → X3) [IsSmooth f2]
  variable (f3 : X3 → X4) [IsSmooth f3]
  variable (f4 : X4 → X5) [IsSmooth f4]
  variable (f5 : X5 → X6) [IsSmooth f5]

  variable (g1 : A1 → A2)
  variable (g2 : A2 → A3)
  variable (g3 : A3 → A4)
  variable (g4 : A4 → A5)
  variable (g5 : A5 → A6)
  
  instance : IsSmooth (λ x => f2 (f1 x)) := sorry -- by infer_instance
  instance : IsSmooth (λ x => f3 (f2 (f1 x))) := by infer_instance

  instance (f : X1 → A2 → X2) [IsSmooth f] (g : X2 → X3) [IsSmooth g] : IsSmooth (λ x1 a2 => g (f x1 a2)) := sorry
  instance (f : X1 → A2 → A3 → X2) [IsSmooth f] (g : X2 → X3) [IsSmooth g] : IsSmooth (λ x1 a2 a3 => g (f x1 a2 a3)) := sorry
  instance (f : X1 → A2 → A3 → A4 → X2) [IsSmooth f] (g : X2 → X3) [IsSmooth g] : IsSmooth (λ x1 a2 a3 a4 => g (f x1 a2 a3 a4)) := sorry

  instance : IsSmooth (λ (f1 : A1 → X2) a => a |> f1) := sorry
  instance : IsSmooth (λ (f1 : A1 → X2) a => a |> f1 |> f2) := by infer_instance
  instance : IsSmooth (λ (f1 : A1 → X2) a => a |> f1 |> f2 |> f3) := by infer_instance
  instance : IsSmooth (λ (f1 : A1 → X2) a => a |> f1 |> f2 |> f3 |> f4) := by infer_instance
  instance : IsSmooth (λ (f1 : A1 → X2) a => a |> f1 |> f2 |> f3 |> f4 |> f5) := by infer_instance

  instance : IsSmooth (λ (f2 : A2 → X3) (g1 : A1 → A2) a => a |> g1 |> f2) := sorry
  instance : IsSmooth (λ (f2 : A2 → X3) (g1 : A1 → A2) a => a |> g1 |> f2 |> f3 |> f4) := by infer_instance
  instance : IsSmooth (λ (f2 : A2 → X3) (g1 : A1 → A2) a => a |> g1 |> f2 |> f3 |> f4 |> f5) := by infer_instance

  instance (g1 : A1 → A2) : IsSmooth (λ (f2 : A2 → X3) a => f2 (g1 a)) := sorry
  instance (g1 : A1 → A2) : IsSmooth (λ (f2 : A2 → X3) a => a |> g1 |> f2 |> f3 |> f4) := by infer_instance
  instance (g1 : A1 → A2) : IsSmooth (λ (f2 : A2 → X3) a => a |> g1 |> f2 |> f3 |> f4 |> f5) := by infer_instance

  instance : IsSmooth (λ (f4 : A4 → X5) a => a |> g1 |> g2 |> g3 |> f4 |> f5) := by infer_instance


  -- instance : IsSmooth (λ (f3 : X3 → X4) x => x |> f1 |> f2 |> f3 |> f4 |> f5) := by infer_instance
  -- instance : IsSmooth (λ (f4 : X4 → X5) x => x |> f1 |> f2 |> f3 |> f4 |> f5) := by infer_instance


  -- instance : IsSmooth (λ (f : Y → Z) (g : X → Y) (x : X) => f (g x)) := sorry
  -- instance  (g : X → Y) : IsSmooth (λ (f : Y → Z) (x : X) => f (g x)) := sorry

  -- instance (f : Y → Z) [IsSmooth f] 
  --          : IsSmooth (λ (g : X → Y) (x : X) => f (g x)) := sorry

  -- instance (f : Y → Z) [IsSmooth f] 
  --          [IsSmooth g] 
  --          : IsSmooth (λ x => f (g x)) := sorry

  -- instance (f : Y → Z) [IsSmooth f]
  --          (h : W → X) [IsSmooth h]
  --          : IsSmooth (λ (g : X → Y) (w : W) => f (g (h w))) := sorry


  -- instance : IsSmooth (@Function.comp X Y Z) := by infer_instance
  -- instance (f : Y → Z) [IsSmooth f] : IsSmooth (λ (g : X → Y) => f ∘ g) := by infer_instance; done
  -- instance (f : Y → Z) [IsSmooth f] [IsSmooth g] : IsSmooth (λ x => (f ∘ g) x) := by simp[Function.comp]; infer_instance; done


  -- instance (f : Y → Z) [IsSmooth f]
  --          (h : W → X) [IsSmooth h]
  --          : IsSmooth (λ (g : X → Y) => f ∘ g ∘ h) := by infer_instance

  -- instance 
  --          (h : W → X)
  --          : IsSmooth (λ (f : Y → Z) (g : X → Y) => f ∘ g ∘ h) := sorry

  -- instance 
  --          (h : W → X) [IsSmooth h]
  --          : IsSmooth (λ (f : Y → Z) (g : X → Y) => f ∘ g ∘ h) := by infer_instance

  -- instance (f : Y → Z) [IsSmooth f]
  --          (h : W → X) [IsSmooth h]
  --          : IsSmooth (λ (g : X → Y) x => f (g (h x))) := by infer_instance

  -- variable (g : X → Y)

  -- -- one extra arg
  -- instance (f : Y → α → Z) (a : α) [IsSmooth (λ y => f y a)] 
  --          [IsSmooth g] 
  --          : IsSmooth (λ x => f (g x) a) := by infer_instance

  -- -- two extra arg
  -- instance (f : Y → α → β → Z) (a : α) (b : β) [IsSmooth (λ y => f y a b)] 
  --          [IsSmooth g] 
  --          : IsSmooth (λ x => f (g x) a b) := by infer_instance

  -- -- three extra arg
  -- instance (f : Y → α → β → γ → Z) (a : α) (b : β) (c : γ) [IsSmooth (λ y => f y a b c)] 
  --          [IsSmooth g] 
  --          : IsSmooth (λ x => f (g x) a b c) := by infer_instance

  -- four extra args
  -- .
  -- .
  -- .

end composition


----------------
-- evaluation --
----------------
-- instance : IsSmooth (λ (f : α → Y) (a : α) => f a) := sorry
-- instance (f : Y → Z) [IsSmooth f] : IsSmooth (λ (g : α → Y) (a : α) => f (g a)) := sorry

-- id
instance : IsSmooth (id : X → X) := sorry
instance : IsSmooth (λ x : X => x) := sorry

-- constant
instance : IsSmooth (λ (x : X) (b : β) => x) := sorry
instance (x : X) : IsSmooth (λ (y : Y) => x) := sorry




-----------------------
-- curry and uncurry --
-----------------------
-- section curry

--   instance (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)] : IsSmooth (λ xy : X×Y => f xy.1 xy.2) := sorry
--   instance (f : X×Y → Z) [IsSmooth f] : IsSmooth (λ x y => f (x,y)) := sorry
--   instance (f : X×Y → Z) [IsSmooth f] : IsSmooth (λ y x => f (x,y)) := sorry

-- end curry

