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

--  ___      _       _   _ _        _   _
-- / __|_  _| |__ __| |_(_) |_ _  _| |_(_)___ _ _
-- \__ \ || | '_ (_-<  _| |  _| || |  _| / _ \ ' \
-- |___/\_,_|_.__/__/\__|_|\__|\_,_|\__|_\___/_||_|

instance : IsLin (@subs α β Z) := sorry
instance (f : α → Y → Z) [∀ a, IsLin (f a)]: IsLin (@subs α Y Z f) := sorry

--- For (subs f g) to be linear, f has to be a sum of two linear functions.
--- There are 8 different ways of writting a sum of two functions - the whole trouble is with identity 
--- x + y
instance (g : X → X) [IsLin g] : IsLin (subs HAdd.hAdd g) := sorry
--- y + x
instance (g : X → X) [IsLin g] : IsLin (subs (swap HAdd.hAdd) g) := sorry
-- f x + y
instance (f : X → Y) (g : X → Y) [IsLin f] [IsLin g] : IsLin (subs (comp HAdd.hAdd f) g) := sorry
-- x + f y
instance (f : Y → X) (g : X → Y) [IsLin f] [IsLin g] : IsLin (subs (swap (comp comp HAdd.hAdd) f) g) := sorry
-- f y + x
instance (f : Y → X) (g : X → Y) [IsLin f] [IsLin g] : IsLin (subs (swap (comp HAdd.hAdd f)) g) := sorry
-- y + f x
instance (f : X → Y) (g : X → Y) [IsLin f] [IsLin g] : IsLin (subs (comp (swap HAdd.hAdd) f) g) := sorry
-- f x + f' y
instance (f : X → Z) (f' : Y → Z) (g : X → Y) [IsLin f] [IsLin f'] [IsLin g] : IsLin (subs (swap (comp comp (comp HAdd.hAdd f)) f') g) := sorry
-- f' y + f x
instance (f : X → Z) (f' : Y → Z) (g : X → Y) [IsLin f] [IsLin f'] [IsLin g] : IsLin (subs (comp (swap (comp HAdd.hAdd f')) f) g) := sorry



--- 
-- instance  (f : Y → X → Z) (g : X → Y) [IsLin (subs (swap f) g)] : IsLin (subs (comp f g) id) := sorry


