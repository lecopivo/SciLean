import SciLean

open SciLean


variable 
  {K : Type} [IsROrC K]
  {X : Type} [Vec K X]
  {Y : Type} [Vec K Y]

set_default_scalar K


variable (f : X → Nat → Y) (x : X)

-- TODO: add option to lsimp not to destroy let bindings with lambdas
-- /--
-- info: let ydf := fun i => ∂ (x':=x), f x' i;
-- ydf 0 : X → Y
-- -/
-- #guard_msgs in
-- #check 
--   (let ydf := fun i => ∂ x':=x, f x' i; (ydf 0))
--   rewrite_by
--     ftrans only

-- /--
-- info: let f := fun i => i;
-- f 0 : ℕ
-- -/
-- #guard_msgs in
-- #check 
--   (let f := fun i : Nat => i ; (f 0))
--   rewrite_by
--     ftrans only

