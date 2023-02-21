import SciLean.Core.Integral

set_option synthInstance.maxSize 2000

namespace SciLean

-- TODO: move this!
instance sum.arg_f.hasAdjoint {X ι} [Enumtype ι] [SemiHilbert X] 
  : HasAdjoint (sum : (ι → X) → X) := by (try infer_instance); sorry_proof
instance sum.arg_f.isLin {X ι} [Enumtype ι] [Vec X] 
  : IsLin (sum : (ι → X) → X) := by (try infer_instance); sorry_proof
instance sum.arg_f.isSmooth {X ι} [Enumtype ι] [Vec X] 
  : IsSmooth (sum : (ι → X) → X) := by infer_instance

instance Basis.basis.arg_x.hasAdjoint {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : HasAdjoint (λ x : X => 𝕡 i x) := by (try infer_instance); sorry_proof
instance Basis.basis.arg_x.isLin {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : IsLin (λ x : X => 𝕡 i x) := by infer_instance
instance Basis.basis.arg_x.isSmooth {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : IsSmooth (λ x : X => 𝕡 i x) := by infer_instance

instance Basis.basis.arg_x.adj_simp {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : adjoint (λ (x : X) => 𝕡 i x) = (λ c => c * 𝕖'[X] i) := sorry_proof

instance DualBasis.dualBasis.arg_x.hasAdjoint {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : HasAdjoint (λ x : X => 𝕡' i x) := by (try infer_instance); sorry_proof
instance DualBasis.dualBasis.arg_x.isLin {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : IsLin (λ x : X => 𝕡' i x) := by infer_instance
instance DualBasis.dualBasis.arg_x.isSmooth {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : IsSmooth (λ x : X => 𝕡' i x) := by infer_instance

instance DualBasis.dualBasis.arg_x.adj_simp {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : adjoint (λ (x : X) => 𝕡' i x) = (λ c => c * 𝕖[X] i) := sorry_proof
  

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

@[autodiff]
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

@[autodiff]
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

@[autodiff]
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

@[simp, autodiff]
theorem Smooth.gradient.arg_f.adj_simp 
  : (Smooth.gradient : (X⟿ℝ) → X⟿X)† 
    =
    - Smooth.divergence
    := sorry_proof


set_option synthInstance.maxSize 2000 in
example  (f : ℝ⟿ℝ) : HasAdjointT fun (g : ℝ⟿ℝ) => fun x ⟿ ⟪ⅆ f x, ⅆ g x⟫ := by infer_instance

-- set_option synthInstance.maxSize 2000 in
-- example  (f : X⟿ℝ) : (fun (g : X⟿ℝ) => fun x ⟿ ⟪∇ f x, ∇ g x⟫)†
--                        = 
--                        λ h => - Smooth.divergence (λ x ⟿ (h x * ∇ f x)) := 
-- by (conv => lhs; symdiff); done

#check Smooth.gradient


