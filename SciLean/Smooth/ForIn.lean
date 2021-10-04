import SciLean.Smooth.Basic
import SciLean.Smooth.Combinators

-- This is not true! 
-- However, it is true for  ((Nat → X ⟿ X) → X → X). So we need to add support for the space of all smooth functions (X ⟿ Y) and add support for (λₛ x : X, f y : (X ⟿ Y)) for smooth f
-- def forIn.is_differentiable_1 {X} [Vec X] (n:Nat) : IsDiff ((comp (swap (@forIn Id _ _ _ _ _ ([0 : n]))) (comp (comp ForInStep.yield))) : ((Nat → X → X) → X → X)) := sorry

instance forIn.is_differentiable_2 {X} [Vec X] (a b : Nat) (f : Nat → X → X) [∀ i, IsDiff (f i)] : IsDiff ((swap (@forIn Id _ _ _ _ _ ([a : b])) (comp (comp ForInStep.yield) f)) : (X → X)) := sorry

@[simp] def forLoop.differential_2 {X} [Vec X] (a b :Nat) (f : Nat → X → X) (x dx : X) [∀ i, IsDiff (f i)] : 
  δ ((swap (@forIn Id _ _ _ _ _ ([a : b])) (comp (comp ForInStep.yield) f)) : (X → X)) x dx 
  = ((do
        let mut xdx := (x, dx)
        for i in [a : b] do
          xdx := (tangent_map (f i)) xdx
        xdx) : X × X).2
:= sorry

