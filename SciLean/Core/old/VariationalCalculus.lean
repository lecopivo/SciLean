import SciLean.Core.Integral
import SciLean.Core.CoreFunctions

namespace SciLean

variable {X Y ι : Type} [EnumType ι] [FinVec X ι] [Hilbert Y] [Hilbert Z]

--------------------------------------------------------------------------------
-- Variational dual
--------------------------------------------------------------------------------

 -- maybe add a condition that φ is test function on Ω
def hasVariationalDual (F : (X ⟿ Y) → Set X → ℝ)
  := ∃ (f : X ⟿ Y), ∀ Ω (φ : X ⟿ Y), F f Ω = ∫ x∈Ω, ⟪f x, φ x⟫

noncomputable
def variationalDual (F : (X ⟿ Y) → Set X → ℝ) : (X ⟿ Y) :=
  match Classical.dec (hasVariationalDual F) with
  | .isTrue h => Classical.choose h
  | .isFalse _ => 0

instance (F : (X ⟿ Y) → Set X → ℝ) : Dagger F (variationalDual F) := ⟨⟩


@[app_unexpander variationalDual] def unexpandVariationalDual : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:term $ys*) => `($f† $ys*)
  | _  => throw ()

#check integral

-- maybe rename to integral.arg_f.variationalDual_rule_comp
@[simp]
theorem variationalDual.arg_F.adjoint_simp (F : (X ⟿ Y) → (X → ℝ)) [∀ f, IsSmooth (F f)] (h : HasAdjoint (λ f => λ x ⟿ F f x) := by infer_instance)
  : (fun f : X ⟿ Y => ∫ x, F f x)†
    =
    (λ f => λ x ⟿ F f x)† 1
  := sorry_proof


--------------------------------------------------------------------------------
-- Variational Gradient
--------------------------------------------------------------------------------

noncomputable
def gradientVariational (F : (X⟿Y) → Set X → ℝ) (f : X⟿Y) := (∂ F f)†

instance (F : (X⟿Y) → Set X → ℝ) : Nabla F (gradientVariational F) := ⟨⟩

@[simp]
theorem gradientVariational_comp (F : (X⟿Y) → (X⟿ℝ))
  : (∇ λ f : X ⟿ Y => ∫ x, (F f).1 x)
    =
    λ f => ∂† F f 1
  := sorry_proof



--------------------------------------------------------------------------------
-- Divergence ∂·
--------------------------------------------------------------------------------

noncomputable
def divergenceDiffSmooth (v : X ⟿ X ⊸ Y) := λ x ⟿ - ∑ i, ∂ v x (𝕖' i) (𝕖 i)

instance (v : X ⟿ X ⊸ Y) : PartialDot v (divergenceDiffSmooth v) := ⟨⟩


--------------------------------------------------------------------------------
-- Divergence ∇·
--------------------------------------------------------------------------------

noncomputable
def divergenceAdjDiffSmooth {Y} {κ} [EnumType κ] [FinVec Y κ] (v : X⟿Y⊸X) :=
  let dv := λ (x : X) (u : X) (u' : Y) => ∂ (x':=x;u), (v.1 x').1 u'
  SmoothMap.mk (λ (x : X) => ∑ (i:κ) (j:ι), 𝕡 j (dv x (𝕖[X] j) (𝕖'[Y] i)) • 𝕖[Y] i) sorry_proof

instance {Y} {κ} [EnumType κ] [FinVec Y κ] (v : X ⟿ Y ⊸ X) : Divergence v (divergenceAdjDiffSmooth v) := ⟨⟩

-- Classical divergence of a vector field

noncomputable
def divergence (v : X→X) : X→ℝ:=
  let dv := λ (x : X) (u : X) => ∂ (x':=x;u), v x'
  (λ (x : X) => ∑ (j:ι), 𝕡 j (dv x (𝕖[X] j)))

noncomputable
def divergenceSmooth (v : X⟿X) : X⟿ℝ :=
  SmoothMap.mk (divergence v.1) sorry_proof

instance (v : X → X) : Divergence v (divergence v) := ⟨⟩

@[default_instance]
instance (v : X ⟿ X) : Divergence v (divergenceSmooth v) := ⟨⟩


--------------------------------------------------------------------------------
-- Unexpanders for differential operators
--------------------------------------------------------------------------------

@[app_unexpander Smooth.differential] def unexpandSmoothDifferential : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:term $xs*) => `(∂ $f:term $xs*)
  | _  => throw ()

@[app_unexpander Smooth.gradient] def unexpandSmoothGradient : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:term $xs*) => `(∇ $f:term $xs*)
  | _  => throw ()

@[app_unexpander divergenceDiffSmooth] def unexpandSmoothDivergenceDiff : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:term $xs*) => `(∂· $f:term $xs*)
  | _  => throw ()

@[app_unexpander divergenceAdjDiffSmooth] def unexpandSmoothDivergenceAdjDiff : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:term $xs*) => `(∇· $f:term $xs*)
  | _  => throw ()

@[app_unexpander divergence] def unexpandDivergence : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:term $xs*) => `(∇· $f:term $xs*)
  | _  => throw ()

@[app_unexpander divergenceSmooth] def unexpandSmoothDivergence : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:term $xs*) => `(∇· $f:term $xs*)
  | _  => throw ()


--------------------------------------------------------------------------------
-- Different forms of divergence
--------------------------------------------------------------------------------

theorem Smooth.divergence.symmetric_form (v : X ⟿ X ⊸ Y)
  : ∂· v
    =
    λ x ⟿ - ∑ i j, ⟪𝕖'[X] i, 𝕖' j⟫ • ∂ v x (𝕖 i) (𝕖 j)
  :=
by
  -- calc
  --   𝕖' i = ∑ j, 𝕡 j (𝕖' i) • 𝕖 j   := by FinVec.is_basis (𝕖' i)
  --      _ = ∑ j, ⟪𝕖' j, 𝕖' i⟫ • 𝕖 j := by ← inner_dualBasis_proj
  -- then it is just linearity
  sorry_proof


--------------------------------------------------------------------------------
-- Divergence as adjoint of differential
--------------------------------------------------------------------------------


-- This is a component wise formulation of divergence theorem
theorem divergence_theorem (f : X ⟿ ℝ)
  (Ω : Set X) (S : Set X) -- ∂ Ω = S -- surface of Ω
  (𝕟 : X → X) -- this should be the normal of Ω
  : ∫ x∈Ω, ∂ f x (𝕖 i)
    =
    ∫ x∈S, f x * ⟪𝕟 x, 𝕖 i⟫ -- not entirelly sure about the projection of the normal, it might be `⟪𝕟 x, 𝕖' i⟫`
  := sorry_proof

@[simp]
theorem Smooth.differential.arg_f.adjoint_simp
  : (Smooth.differential : (X⟿Y) → (X⟿X⊸Y))†
    =
    - divergenceDiffSmooth
  :=
by

  -- this is a setup for proving adjoint
  have Ω : Set X := sorry  -- this should be sufficiently regular, can be even a ball sufficently big to contain support of `v`
  have f : X ⟿ Y := sorry
  have v : X⟿X⊸Y := sorry -- this should be a test function vanishing outside of Ω
  have : ∫ x∈Ω, ⟪∂ f x, v x⟫ = - ∫ x∈Ω, ⟪f x, ∂· v x⟫ := by
   calc
     ∫ x∈Ω, ⟪∂ f x, v x⟫ = ∫ x∈Ω, ∑ i, ⟪∂ f x (𝕖 i), v x (𝕖' i)⟫ := by sorry_proof

     -- change of notation
     _ = ∫ x∈Ω, ∑ i, ⟪(∂ (x':=x;𝕖 i), f.1 x'), v x (𝕖' i)⟫ := by sorry_proof

     -- product rule for differentiation
     _ = ∫ x∈Ω, ∑ i, (∂ (x':=x;𝕖 i), ⟪f x', v x' (𝕖' i)⟫
                      -
                      ⟪f x, (∂ (x':=x;𝕖 i), v x' (𝕖' i))⟫) := by sorry_proof

     -- first therm vanishes by using greens theorem and the fact `v` vanishes on the boundary of Ω
     _ = - ∫ x∈Ω, ∑ i, ⟪f x, (∂ (x':=x;𝕖 i), v x' (𝕖' i))⟫ := by sorry_proof

     -- change of notation and push sum inside
     _ = - ∫ x∈Ω, ⟪f x, ∑ i, (∂ v x (𝕖' i) (𝕖 i))⟫ := by sorry_proof

     -- definition of divergence
     _ = - ∫ x∈Ω, ⟪f x, ∂· v x⟫ := by sorry_proof

  sorry_proof


@[simp]
theorem Smooth.adjointDifferential.arg_f.adjoint_simp {Y} {κ} [EnumType κ] [FinVec Y κ]
  : (Smooth.adjointDifferential : (X⟿Y) → (X⟿Y⊸X))†
    =
    - divergenceAdjDiffSmooth
  :=
by

  -- this is a setup for proving adjoint
  have Ω : Set X := sorry  -- this should be sufficiently regular, can be even a ball sufficently big to contain support of `v`
  have f : X ⟿ Y := sorry
  have v : X⟿Y⊸X := sorry -- this should be a test function vanishing outside of Ω
  have : ∫ x∈Ω, ⟪∂† f x, v x⟫ = - ∫ x∈Ω, ⟪f x, ∇· v x⟫ := by
   calc
     ∫ x∈Ω, ⟪∂† f x, v x⟫ = ∫ x∈Ω, ∑ i, ⟪∂† f x (𝕖 i), v x (𝕖' i)⟫ := by sorry_proof

     -- adjoint of differential
     _ = ∫ x∈Ω, ∑ i, ⟪𝕖 i, ∂ f x (v x (𝕖' i))⟫ := by sorry_proof

     -- change of notation
     _ = ∫ x∈Ω, ∑ i, ⟪𝕖 i, (∂ (x':=x;(v x (𝕖' i))), f.1 x')⟫ := by sorry_proof

     -- pull out derivative
     _ = ∫ x∈Ω, ∑ i, ∂ (x':=x;(v x (𝕖' i))), ⟪𝕖 i, f.1 x'⟫ := by sorry_proof

     -- rewrite (v x (𝕖' i)) into a basis
     _ = ∫ x∈Ω, ∑ i j, 𝕡 j (v x (𝕖' i)) * ∂ (x':=x;𝕖 j), ⟪𝕖 i, f.1 x'⟫ := by sorry_proof

     -- product rule for differentiation
     _ = ∫ x∈Ω, ∑ i j, (∂ (x':=x;𝕖 j), 𝕡 j (v x' (𝕖' i)) * ⟪𝕖 i, f.1 x'⟫
                        -
                        (𝕡 j (∂ (x':=x;𝕖[X] j), v x' (𝕖' i))) * ⟪𝕖 i, f.1 x⟫) := by sorry_proof

     -- the frist term dissapears thanks to the divergence theorem
     _ = - ∫ x∈Ω, ∑ i j, - (𝕡 j (∂ (x':=x;𝕖[X] j), v x' (𝕖' i))) * ⟪𝕖 i, f.1 x⟫ := by sorry_proof

     -- definition of divergenceAdjDiff + `⟪x,y⟫ = ∑ i, ⟪𝕖' i, x⟫ * ⟪𝕖 i, y⟫`
     _ = - ∫ x∈Ω, ⟪f x, ∇· v x⟫ := by sorry_proof

  sorry_proof


@[simp]
theorem Smooth.gradient.arg_f.adjoint_simp
  : (Smooth.gradient : (X⟿ℝ) → (X⟿X))†
    =
    - divergenceSmooth
  := sorry_proof


@[simp]
theorem Smooth.differentialScalar.arg_f.adjoint_simp {X} [Hilbert X]
  : (Smooth.differentialScalar : (ℝ⟿X) → (ℝ⟿X))†
    =
    - Smooth.differentialScalar
  := sorry_proof
