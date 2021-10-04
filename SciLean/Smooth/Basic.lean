import SciLean.Prelude 

variable {α β γ : Type} 
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

instance differential_is_linear (f : X → Y) (x : X) [IsDiff f] : IsLin (δ f x) := sorry

-- Product - Prod.fst and Prod.snd is already in Lin but we are missing Prod.mk
instance : IsDiff (Prod.mk : X → Y → X × Y) := sorry
instance (x : X) : IsDiff (Prod.mk x : Y → X × Y) := sorry
@[simp] def Prod.mk.differential_1 (x dx : X) (y : Y) : δ Prod.mk x dx y = (dx, 0) := sorry
@[simp] def Prod.mk.differential_2 (x : X) (y dy : Y) : δ (Prod.mk x) y dy = (0, dy) := sorry

-- Differentiation of linear f
instance (f : X → Y) [IsLin f] : IsDiff f := sorry
@[simp] def differential_of_linear (f : X → Y) (x dx : X) [IsLin f] : δ f x dx = f dx := sorry

-- Differentiation of inverse f
instance (f : X → Y) [IsDiff f] [IsInv f] [∀ x, IsInv (δ f x)] : IsDiff f⁻¹ := sorry
@[simp] def differential_of_inverse (f : X → Y) (y dy : Y) [IsDiff f] [IsInv f] [IsInv (δ f (f⁻¹ y))] : δ (f⁻¹) y dy = (δ f (f⁻¹ y))⁻¹ dy := sorry

section Arithmetics

  -- Differentiation of multiplication should be infered by linearity
  instance : IsDiff (HMul.hMul : ℝ → X → X) := sorry
  instance (r : ℝ) : IsDiff (HMul.hMul r : X → X) := sorry


  instance : IsDiff (HAdd.hAdd : X → X → X) := sorry
  instance (x : X) : IsDiff (HAdd.hAdd x : X → X) := sorry

  @[simp] def HAdd.hAdd.differential_1 (x dx y : X) : δ HAdd.hAdd x dx y = dx := sorry
  @[simp] def HAdd.hAdd.differential_2 (x y dy : X) : δ (HAdd.hAdd x ) y dy = dy := sorry

end Arithmetics


--------------
--  ___                _   _      __  __
-- / __|_ __  ___  ___| |_| |_   |  \/  |__ _ _ __ ___
-- \__ \ '  \/ _ \/ _ \  _| ' \  | |\/| / _` | '_ (_-<
-- |___/_|_|_\___/\___/\__|_||_| |_|  |_\__,_| .__/__/
--                                           |_|
 -- define (X ⇀ Y) 
--- define (X ⤳ Y) 
--- define (X ⟿ Y)


--- auto_proof := by simp; rmlamlet; infer_instance
--- Totaly do λₛ (f : Y ⟿ Z) (g : X ⟿ Y) (x : X), f (g x) = ⟨ λ (f : Y → Z) => ⟨ λ (g : X → Y) => ⟨λ x : X => f (g x) , by auto_proof⟩ , by auto_proof⟩, by auto_proof⟩ 
