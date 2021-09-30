-- import SciLean.Linear.Basic

-- -- set_option trace.Meta.synthInstance true
-- -- set_option synthInstance.maxHeartbeats 500

-- instance {U} (u : U) [Hilbert U] : IsLin (Inner.inner u) := sorry
-- instance {U} (u : U) [Hilbert U] : IsLin (swap Inner.inner u) := sorry

-- def adjoint {U V} : (U → V) → (V → U) := sorry

-- prefix:120 "†" => adjoint

-- namespace adjoint

-- variable {U V W} [Hilbert U] [Hilbert V] [Hilbert W] -- [Vec U] [Vec V] [Vec W] [Inner U] [Inner V] [Inner W]

-- @[simp] def definition (f : U → V) (u : U) (v : V) [IsLin f] : ⟨adjoint f v, u⟩ = ⟨v, f u⟩ := sorry

-- @[simp] def comp (f : V → W) (g : U → V) [IsLin f] [IsLin g] : †(comp f g) = comp (†g) (†f) := 
-- by 
--   funext u; apply inner.ext; intros; simp

-- @[simp] def inner (u : U) (c : ℝ) : adjoint (Inner.inner u : U → ℝ) c = c * u := 
-- by
--   apply inner.ext; intros; simp; rw [← inner.mul]

-- end adjoint
