import SciLean.Core.IntegralProperties


set_option synthInstance.maxSize 2000

namespace SciLean


--------------------------------------------------------------------------------
-- Divergence
--------------------------------------------------------------------------------

/-- This divergence is an adjoint of `∇ : (X⟿ℝ) → (X⟿X)` -/
noncomputable
def divergence {X ι} [Enumtype ι] [FinVec X ι] (f : X→X) : X→ℝ :=
  λ x => ∑ i, 𝕡 i (∂ f x (𝕖[X] i))  -- ⟪∂ f x (e[X] i), 𝕖'[X] i⟫

/-- This divergence is an adjoint of `∇ : (X⟿ℝ) → (X⟿X)` -/
noncomputable
def Smooth.divergence {X ι} [Enumtype ι] [FinVec X ι] (f : X⟿X) : X⟿ℝ :=
  λ x ⟿ ∑ i, 𝕡 i (∂ f x (𝕖[X] i))  -- ⟪∂ f x (e[X] i), 𝕖'[X] i⟫

instance Smooth.divergence.instDivergenceNotation
  {X ι} [Enumtype ι] [FinVec X ι] (f : X⟿X)
  : Divergence f (Smooth.divergence f) := ⟨⟩


/-- This divergence is an adjoint of `∂ : (X⟿Y) → (X⟿X⊸Y)` -/
noncomputable
def divergenceDual {X Y ι} [Enumtype ι] [FinVec X ι] [Vec Y] (f : X→X→Y) : X→Y :=
  λ x => ∑ i, ∂ f x (𝕖'[X] i) (𝕖'[X] i)

/-- This divergence is an adjoint of `∂ : (X⟿Y) → (X⟿X⊸Y)` -/
noncomputable
def Smooth.divergenceDual {X Y ι} [Enumtype ι] [FinVec X ι] [Vec Y] (f : X⟿X⊸Y) : X⟿Y :=
  λ x ⟿ ∑ i, ∂ f x (𝕖'[X] i) (𝕖'[X] i)

instance Smooth.divergenceDual.instDivergenceNotation
  {X Y ι} [Enumtype ι] [FinVec X ι] [Vec Y] (f : X⟿X⊸Y)
  : Divergence f (Smooth.divergenceDual f) := ⟨⟩

--------------------------------------------------------------------------------
-- Divergence - properties
--------------------------------------------------------------------------------

variable {X Y ι} [Enumtype ι] [FinVec X ι] [Hilbert Y]

-- Divergence

instance Smooth.divergence.arg_f.hasAdjoint
  : HasAdjoint (Smooth.divergence : (X⟿X) → (X⟿ℝ)) := sorry_proof
instance Smooth.divergence.arg_f.isLin
  : IsLin (Smooth.divergence : (X⟿X) → (X⟿ℝ)) := by infer_instance
instance Smooth.divergence.arg_f.isSmooth
  : IsSmooth (Smooth.divergence : (X⟿X) → (X⟿ℝ)) := by infer_instance

@[diff]
theorem Smooth.divergence.arg_f.adj_simp  
  : (Smooth.divergence : (X⟿X) → (X⟿ℝ))†
    =
    - Smooth.gradient := sorry_proof


-- Divergence Dual

instance Smooth.divergenceDual.arg_f.hasAdjoint
  : HasAdjoint (Smooth.divergenceDual : (X⟿X⊸Y) → (X⟿Y)) := sorry_proof
instance Smooth.divergenceDual.arg_f.isLin
  : IsLin (Smooth.divergenceDual : (X⟿X⊸Y) → (X⟿Y)) := by infer_instance
instance Smooth.divergenceDual.arg_f.isSmooth
  : IsSmooth (Smooth.divergenceDual : (X⟿X⊸Y) → (X⟿Y)) := by infer_instance

@[diff]
theorem Smooth.divergenceDual.arg_f.adj_simp  
  : (Smooth.divergenceDual : (X⟿X⊸Y) → (X⟿Y))†
    =
    - Smooth.differential := sorry_proof


--------------------------------------------------------------------------------
-- Differential - properties
--------------------------------------------------------------------------------

instance Smooth.differential.arg_f.hasAdjoint
  : HasAdjoint (Smooth.differential : (X⟿Y) → X⟿X⊸Y) := by (try infer_instance); sorry_proof
instance Smooth.differential.arg_f.isLin {X Y} [Vec X] [Vec Y]
  : IsLin (Smooth.differential : (X⟿Y) → X⟿X⊸Y) := by (try infer_instance); sorry_proof
instance Smooth.differential.arg_f.isSmooth {X Y} [Vec X] [Vec Y]
  : IsSmooth (Smooth.differential : (X⟿Y) → X⟿X⊸Y) := by infer_instance

theorem Smooth.differential.arg_f.adj_simp {X Y ι} [Enumtype ι] [FinVec X ι] [Hilbert Y]
  : (Smooth.differential : (X⟿Y) → X⟿X⊸Y)†
    =
    - Smooth.divergenceDual
    := sorry_proof


--------------------------------------------------------------------------------
-- Differential Scalar - properties
--------------------------------------------------------------------------------

instance Smooth.differentialScalar.arg_f.hasAdjoint {X} [Hilbert X] 
  : HasAdjoint (λ (f : ℝ⟿X) => ⅆ f) := by (try infer_instance); sorry_proof
instance Smooth.differentialScalar.arg_f.isLin {X} [Vec X] 
  : IsLin (Smooth.differentialScalar : (ℝ⟿X) → ℝ⟿X) := by (try infer_instance); sorry_proof 
instance Smooth.differentialScalar.arg_f.isSmooth {X} [Vec X] 
  : IsSmooth (Smooth.differentialScalar : (ℝ⟿X) → ℝ⟿X) := by infer_instance

@[diff]
theorem Smooth.differentialScalar.arg_f.adj_simp {X} [Hilbert X] 
  : (Smooth.differentialScalar : (ℝ⟿X) → (ℝ⟿X))†
    =
    - Smooth.differentialScalar
    := sorry_proof


--------------------------------------------------------------------------------
-- Differential Scalar - properties
--------------------------------------------------------------------------------

instance Smooth.gradient.arg_f.hasAdjoint
  : HasAdjoint (Smooth.gradient : (X⟿ℝ) → (X⟿X)) := by (try infer_instance); sorry_proof
instance Smooth.gradient.arg_f.isLin {X} [SemiHilbert X] 
  : IsLin (Smooth.gradient : (X⟿ℝ) → (X⟿X)) := by (try infer_instance); sorry_proof 
instance Smooth.gradient.arg_f.isSmooth {X} [SemiHilbert X] 
  : IsSmooth (Smooth.gradient : (X⟿ℝ) → (X⟿X)) := by infer_instance

@[diff]
theorem Smooth.gradient.arg_f.adj_simp 
  : (Smooth.gradient : (X⟿ℝ) → X⟿X)† 
    =
    - Smooth.divergence
    := sorry_proof


--------------------------------------------------------------------------------
-- doodle
--------------------------------------------------------------------------------

set_option synthInstance.maxSize 2000 in
example  (f : ℝ⟿ℝ) : (fun (g : ℝ⟿ℝ) => fun x ⟿ ⟪f x, ⅆ g x⟫)†
                       = 
                       λ h => - ⅆ (λ x ⟿ h x * f x) := by symdiff; done


set_option synthInstance.maxSize 2000 in
example  (f : ℝ⟿ℝ) : HasAdjointT fun (g : ℝ⟿ℝ) => fun x ⟿ ⟪ⅆ f x, ⅆ g x⟫ := by infer_instance

-- set_option synthInstance.maxSize 2000 in
example  (f : X⟿ℝ) : (fun (g : X⟿ℝ) => fun x ⟿ ⟪∇ f x, ∇ g x⟫)†
                       = 
                       λ h : X⟿ℝ => - ∇· (λ x ⟿ (h x * ∇ f x)) := by symdiff; done


@[diff]
theorem hahah {X Y Z} [Vec X] [Vec Y] [Vec Z]
  (f : X → Y → Z) [IsSmoothNT 2 f]
  : ∂ (λ x => λ y ⟿ f x y) = λ x dx => λ y ⟿ (∂ f) x dx y := sorry_proof

@[simp, diff_simp]
theorem differential_zero_dir {X Y} [Vec X] [Vec Y]
  (f : X → Y) [IsSmooth f] (x)
  : ∂ f x 0 = 0 := sorry_proof

#check integral.arg_f.isLin

example : ∂ (fun (g : X⟿ℝ) => ∫ x, ∥∇ g x∥²)
          =
          λ g dg : X⟿ℝ => ∫ x, 2 * ⟪∇ dg x, ∇ g x⟫ :=
by symdiff; done


attribute [default_instance] Smooth.gradient.instNablaNotation
        
-- set_option trace.Meta.Tactic.simp.discharge true in


example : ∇ (g : X⟿ℝ), ∫ x, (1/2:ℝ) * ∥∇ g x∥²
          = 
          λ g : X⟿ℝ => - ∇· (∇ g) := 
by unfold variationalGradient
   symdiff; symdiff; simp only [uncurryN, Prod.Uncurry.uncurry];
   simp only [(sorry_proof : ∀ x y : X, ⟪x,y⟫ = ⟪y,x⟫)];
   symdiff
   done


