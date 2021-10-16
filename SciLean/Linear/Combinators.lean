import SciLean.Linear.Basic

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

--  ___    _         _   _ _
-- |_ _|__| |___ _ _| |_(_) |_ _  _
--  | |/ _` / -_) ' \  _| |  _| || |
-- |___\__,_\___|_||_\__|_|\__|\_, |
--                             |__/

instance : IsLin (id : X → X) := sorry

--   ___             _            _
--  / __|___ _ _  __| |_ __ _ _ _| |_
-- | (__/ _ \ ' \(_-<  _/ _` | ' \  _|
--  \___\___/_||_/__/\__\__,_|_||_\__|

instance : IsLin (const β : X → β → X) := sorry
instance : IsLin (const Y (0 : X) : Y → X) := sorry

--  ___
-- / __|_ __ ____ _ _ __
-- \__ \ V  V / _` | '_ \
-- |___/\_/\_/\__,_| .__/
--                 |_|

instance : IsLin (@swap α β Z) := sorry
instance (f : α → Y → Z) [∀ a, IsLin (f a)] : IsLin (swap f) := sorry
instance (f : X → β → Z) (b : β) [IsLin f] : IsLin (swap f b) := sorry

-- -- reduction instances
-- instance (f : β → X → Y) (g : α → β) (a : α)  [IsLin (f (g a))] : IsLin (comp f g a) := sorry
-- -- Is this one really necessary??
-- instance (f : β → γ → X → Y) (g : α → β) (a : α) (c : γ)  [IsLin (f (g a) c)] : IsLin (comp f g a c) := sorry 

--   ___                        _ _   _
--  / __|___ _ __  _ __  ___ __(_) |_(_)___ _ _
-- | (__/ _ \ '  \| '_ \/ _ (_-< |  _| / _ \ ' \
--  \___\___/_|_|_| .__/\___/__/_|\__|_\___/_||_|
--                |_|
instance : IsLin (@comp α β Z) := sorry
instance (f : Y → Z) [IsLin f] : IsLin (@comp α _ _ f) := sorry
instance (f : Y → Z) (g : X → Y) [IsLin f] [IsLin g] : IsLin (comp f g) := sorry

--  ___  _                         _
-- |   \(_)__ _ __ _ ___ _ _  __ _| |
-- | |) | / _` / _` / _ \ ' \/ _` | |
-- |___/|_\__,_\__, \___/_||_\__,_|_|
--             |___/

instance : IsLin (@diag α Y) := sorry

-- instance (f : X → X → Y) [only if f = A x + B x where A B are linear]: IsLin (diag f) := sorry
instance : IsLin (diag (HAdd.hAdd : X → X → X)) := sorry

instance (f : X → X) [IsLin f] : IsLin (diag (HAdd.hAdd • f : X → X → X)) := sorry
instance (f : X → X) [IsLin f] : IsLin (diag (comp (swap comp f) HAdd.hAdd : X → X → X)) := sorry

-- arghh getting a bit compilcated :( 
instance (f g : X → Y) [IsLin f] [IsLin g] : IsLin (diag (comp (swap comp f) (HAdd.hAdd • g) : X → X → Y)) := sorry

-- Rebracketed version. It does not seem to be needed right now. Will it bite back?
-- instance (f g : X → Y) [IsLin f] [IsLin g] : IsLin (diag ((comp (swap comp f) HAdd.hAdd) • g : X → X → Y)) := sorry


