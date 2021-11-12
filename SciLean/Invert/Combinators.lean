import SciLean.Invert.Basic

variable {α β γ : Type}

--  ___    _         _   _ _
-- |_ _|__| |___ _ _| |_(_) |_ _  _
--  | |/ _` / -_) ' \  _| |  _| || |
-- |___\__,_\___|_||_\__|_|\__|\_, |
--                             |__/

instance : IsInv (id : α → α) := sorry

@[simp] def id.inverse : (id : α → α)⁻¹ = (id : α → α) := sorry

--   ___             _            _
--  / __|___ _ _  __| |_ __ _ _ _| |_
-- | (__/ _ \ ' \(_-<  _/ _` | ' \  _|
--  \___\___/_||_/__/\__\__,_|_||_\__|

instance (b : β) : IsInv (swap (const β) b : α → α) := sorry

@[simp] def const.inverse : (swap (const β) b : α → α)⁻¹ = id  := sorry


--  ___
-- / __|_ __ ____ _ _ __
-- \__ \ V  V / _` | '_ \
-- |___/\_/\_/\__,_| .__/
--                 |_|

instance : IsInv (@swap α β γ) := sorry

@[simp] def swap.inverse : (@swap α β γ)⁻¹ = (@swap β α γ) := sorry


--   ___                        _ _   _
--  / __|___ _ __  _ __  ___ __(_) |_(_)___ _ _
-- | (__/ _ \ '  \| '_ \/ _ (_-< |  _| / _ \ ' \
--  \___\___/_|_|_| .__/\___/__/_|\__|_\___/_||_|
--                |_|
instance (f : β → β) [IsInv f] : IsInv (@comp α _ _ f) := sorry
instance (g : α → α) [IsInv g] : IsInv (swap (@comp _ _ γ) g) := sorry
instance (f : β → γ) (g : α → β) [IsInv f] [IsInv g] : IsInv (comp f g) := sorry

@[simp] def comp.inverse_1 (f : β → β) [IsInv f] : (@comp α _ _ f)⁻¹ = (@comp α _ _ f⁻¹) := sorry
@[simp] def comp.inverse_2 (g : α → α) [IsInv g] : (swap (@comp _ _ γ) g)⁻¹ = (swap (@comp _ _ γ) g⁻¹) := sorry
@[simp] def comp.inverse_3  (f : β → γ) (g : α → β) [IsInv f] [IsInv g] : (comp f g)⁻¹ = (comp g⁻¹ f⁻¹) := sorry


--  ___      _       _   _ _        _   _
-- / __|_  _| |__ __| |_(_) |_ _  _| |_(_)___ _ _
-- \__ \ || | '_ (_-<  _| |  _| || |  _| / _ \ ' \
-- |___/\_,_|_.__/__/\__|_|\__|\_,_|\__|_\___/_||_|


--- ? can we say something sensible ?
