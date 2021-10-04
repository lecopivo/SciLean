-- import SciLean.Affine.Basic
-- import SciLean.Linear.Combinators
-- universe u' v' w'
-- import SciLean.Algebra

-- variable {α : Type} {β : Type} {γ : Type}
-- variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]

-- --  ___    _         _   _ _
-- -- |_ _|__| |___ _ _| |_(_) |_ _  _
-- --  | |/ _` / -_) ' \  _| |  _| || |
-- -- |___\__,_\___|_||_\__|_|\__|\_, |
-- --                             |__/

-- instance : IsAff (id : X → X) := by infer_instance

-- --   ___             _            _
-- --  / __|___ _ _  __| |_ __ _ _ _| |_
-- -- | (__/ _ \ ' \(_-<  _/ _` | ' \  _|
-- --  \___\___/_||_/__/\__\__,_|_||_\__|

-- instance : IsAff (const β : X → β → X) := by infer_instance
-- instance (x : X) : IsAff (const Y x : Y → X) := sorry

-- --  ___
-- -- / __|_ __ ____ _ _ __
-- -- \__ \ V  V / _` | '_ \
-- -- |___/\_/\_/\__,_| .__/
-- --                 |_|

-- instance : IsAff (@swap α β Z) := by infer_instance
-- instance (f : α → Y → Z) [∀ a, IsAff (f a)] : IsAff (swap f) := sorry
-- instance (f : X → β → Z) (b : β) [IsAff f] : IsAff (swap f b) := sorry

-- --   ___                        _ _   _
-- --  / __|___ _ __  _ __  ___ __(_) |_(_)___ _ _
-- -- | (__/ _ \ '  \| '_ \/ _ (_-< |  _| / _ \ ' \
-- --  \___\___/_|_|_| .__/\___/__/_|\__|_\___/_||_|
-- --                |_|
-- instance : IsAff (@comp α β Z) := by (apply instIsAff)
-- instance (f : Y → Z) [IsAff f] : IsAff (@comp α _ _ f) := sorry
-- instance (f : Y → Z) (g : X → Y) [IsAff f] [IsAff g] : IsAff (comp f g) := sorry


-- --  ___      _       _   _ _        _   _
-- -- / __|_  _| |__ __| |_(_) |_ _  _| |_(_)___ _ _
-- -- \__ \ || | '_ (_-<  _| |  _| || |  _| / _ \ ' \
-- -- |___/\_,_|_.__/__/\__|_|\__|\_,_|\__|_\___/_||_|

-- instance : IsAff (@subs α β Z) := by infer_instance
-- instance (f : α → Y → Z) [∀ a, IsAff (f a)]: IsAff (@subs α Y Z f) := sorry
-- instance (f : X → Y → Z) (g : X → Y) [IsAff f] [∀ x, IsAff (f x)] [IsAff g] : IsAff (subs f g) := sorry

