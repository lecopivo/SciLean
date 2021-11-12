import SciLean.Prelude

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

-- @[simp] def inverse_inverse_1 (f : α → β) (a : α) [IsInv f] : f⁻¹ (f a) = a := sorry
-- @[simp] def inverse_inverse_2 (f : α → β) (a : α) [IsInv f] : f (f⁻¹ b) = b := sorry

def prove_inverse (f : α → β) (a : α) (b : β) [IsInv f] : b = f a → f⁻¹ b = a := sorry

-- Product -- pairing with Unit is invertible
instance : IsInv (Prod.fst : α × Unit → α) := sorry
instance : IsInv (Prod.snd : Unit × α → α) := sorry
instance : IsInv (Prod.mk : α → Unit → α × Unit) := sorry
instance : IsInv (Prod.mk () : α → Unit × α) := sorry

@[simp] def Prod.fst.inverse : (Prod.fst : α × Unit → α)⁻¹ = swap Prod.mk () := by funext x; rw [prove_inverse]; simp
@[simp] def Prod.snd.inverse : (Prod.snd : Unit × α → α)⁻¹ = Prod.mk () := by funext x; rw [prove_inverse]; simp

-- #check (λ a : Unit → α × Unit => (a ()).1)
@[simp] def Prod.mk.inverse_1 : (Prod.mk : α → Unit → α × Unit)⁻¹ = (λ a => (a ()).1) := sorry
@[simp] def Prod.mk.inverse_2 : (Prod.mk () : α → Unit × α)⁻¹ = Prod.snd := sorry

--- Multiplication 
instance (r : ℝ) [NonZero r] : IsInv (HMul.hMul r : X → X) := sorry
instance (r : ℝ) [NonZero r] : IsInv (swap HMul.hMul r : ℝ → ℝ) := sorry

@[simp] def HMul.hMul.inverse_1 (r : ℝ) [NonZero r] : (HMul.hMul r : X → X)⁻¹ = (λ y : X => (1/r)*y) := sorry
@[simp] def HMul.hMul.inverse_1.rels (r : ℝ) [NonZero r] : (HMul.hMul r : ℝ → ℝ)⁻¹ = (λ y : ℝ => y/r) := sorry
@[simp] def HMul.hMul.inverse_2 (r : ℝ) [NonZero r] : (swap HMul.hMul r : ℝ → ℝ)⁻¹ = (λ y : ℝ => y/r ) := sorry

--- Adition 
instance : IsInv (HAdd.hAdd x : X → X) := sorry
instance : IsInv (swap HAdd.hAdd x : X → X) := sorry

@[simp] def HAdd.hAdd.inverse_1 (x : X) : (HAdd.hAdd x : X → X)⁻¹ = λ y => (-x) + y := sorry
@[simp] def HAdd.hAdd.inverse_2 (x : X) : (swap HAdd.hAdd x : X → X)⁻¹ = λ y => y + (-x) := sorry

