import SciLean.Smooth.Basic

variable {α β γ : Type} 
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

--  ___    _         _   _ _
-- |_ _|__| |___ _ _| |_(_) |_ _  _
--  | |/ _` / -_) ' \  _| |  _| || |
-- |___\__,_\___|_||_\__|_|\__|\_, |
--                             |__/

-- Identity is already handled by Lin


--   ___             _            _
--  / __|___ _ _  __| |_ __ _ _ _| |_
-- | (__/ _ \ ' \(_-<  _/ _` | ' \  _|
--  \___\___/_||_/__/\__\__,_|_||_\__|

instance : IsDiff (const β : X → β → X) := sorry
instance (x : X) : IsDiff (const Y x : Y → X) := sorry

@[simp] def const.differential_1 (x dx : X) (b : β) : δ (const β) x dx b = dx := sorry
@[simp] def const.differential_2 (x : X) (y dy : Y) : δ (const Y x) y dy = 0 := sorry

--  ___
-- / __|_ __ ____ _ _ __
-- \__ \ V  V / _` | '_ \
-- |___/\_/\_/\__,_| .__/
--                 |_|

instance : IsDiff (swap : (α → β → Z) → (β → α → Z)) := sorry
instance (f : α → Y → Z) [∀ a, IsDiff (f a)] : IsDiff (swap f) := sorry
instance (f : X → β → Z) (b : β) [IsDiff f] : IsDiff (swap f b) := sorry

-- reduction instances -- not necessary anymore - solved wtih FetchProof
-- instance (f : α → β → X → Y) (a : α) (b : β) [IsDiff (f a b)] : IsDiff (swap f b a) := sorry

@[simp] def swap.differential_1 (f df : α → β → Z) : δ (swap) f df = swap df := sorry
@[simp] def swap.differential_2 (f : α → Y → Z) (a : α) (y dy : Y) [IsDiff (f a)] : δ (swap f) y dy a = δ (f a) y dy := sorry
@[simp] def swap.differential_3 (f : X → β → Z) (x dx : X) (b : β) [IsDiff f] : δ (swap f b) x dx = δ f x dx b := sorry


--   ___                        _ _   _
--  / __|___ _ __  _ __  ___ __(_) |_(_)___ _ _
-- | (__/ _ \ '  \| '_ \/ _ (_-< |  _| / _ \ ' \
--  \___\___/_|_|_| .__/\___/__/_|\__|_\___/_||_|
--                |_|

instance : IsDiff (comp : (β → Z) → (α → β) → (α → Z)) := sorry 
instance (f : Y → Z) [IsDiff f] : IsDiff (comp f : (α → Y) → (α → Z)) := sorry
instance (f : Y → Z) (g : X → Y) [IsDiff f] [IsDiff g] : IsDiff (comp f g) := sorry

-- reduction instances -- not necessary anymore - solved wtih FetchProof
-- instance (f : β → X → Y) (g : α → β) (a : α)  [IsDiff (f (g a))] : IsDiff (comp f g a) := sorry
-- instance (f : β → γ → X → Y) (g : α → β) (a : α) (c : γ)  [IsDiff (f (g a) c)] : IsDiff (comp f g a c) := sorry 

@[simp] def comp.differential_1 (f df : β → Z) : δ (@comp α _ _) f df = comp df := sorry
@[simp] def comp.differential_2 (f : Y → Z) (g dg : α → Y) (a : α) [IsDiff f] : δ (comp f) g dg a = δ f (g a) (dg a) := sorry
@[simp] def comp.differential_3 (f : Y → Z) (g : X → Y) (x dx : X) [IsDiff f] [IsDiff g] : δ (comp f g) x dx = δ f (g x) (δ g x dx) := sorry


--  ___      _       _   _ _        _   _
-- / __|_  _| |__ __| |_(_) |_ _  _| |_(_)___ _ _
-- \__ \ || | '_ (_-<  _| |  _| || |  _| / _ \ ' \
-- |___/\_,_|_.__/__/\__|_|\__|\_,_|\__|_\___/_||_|

instance : IsDiff (@subs α β Z) := sorry
instance (f : α → Y → Z) [∀ a, IsDiff (f a)]: IsDiff (@subs α Y Z f) := sorry
instance (f : X → Y → Z) (g : X → Y) [IsDiff f] [∀ x, IsDiff (f x)] [IsDiff g] : IsDiff (subs f g) := sorry

-- reduction instance -- not necessary anymore - solved wtih FetchProof
-- instance (f : α → β → X → Y) (g : α → β) (a : α) [IsDiff ((f a) (g a))] : IsDiff (subs f g a) := sorry
-- instance (f : α → β → γ → X → Y) (g : α → β) (a : α) (c : γ) [IsDiff ((f a) (g a) c)] : IsDiff (subs f g a c) := sorry

@[simp] def subs.differential_1 (f df : α → β → Z) : δ subs f df = subs df := sorry
@[simp] def subs.differential_2 (f : α → Y → Z) (g dg : α → Y) (a : α) [IsDiff (f a)] : δ (subs f) g dg a = δ (f a) (g a) (dg a) := sorry
@[simp] def subs.differential_3 (f : X → Y → Z) (g : X → Y) (x dx : X) [IsDiff f] [IsDiff (f x)] [IsDiff g] : δ (subs f g) x dx = δ f x dx (g x) + δ (f x) (g x) (δ g x dx) := sorry


