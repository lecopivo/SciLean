import SciLean
import SciLean.Core.Complexify
import SciLean.Meta.DerivingAlgebra
import SciLean.Solver.Solver
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp

open SciLean

variable {X : Type} [Hilbert X]

namespace AbstractManifolGalerkin

  -- structure ApproxSolution {X} [Vec X] (spec : X → Prop) where
  --   approx : ℕ → X
  --   proof : spec (limit val)

  -- structure Solution {X} [Vec X] (spec : X → Prop) where
  --   approx : X
  --   proof : spec val

  -- -- variable {X : Type} [Hilbert X]
  -- variable {U : ℕ → Type} [∀ n, Vec (U n)]


  -- def manifoldGalerkinSolution (f : X → X) (x₀ : X) (p : (n : ℕ) → U n → X) [∀ n, IsSmooth (p n)] (n : ℕ) :=
  --   Solution (λ (uₙ : ℝ → U n) => 
  --       (∀ v t, ⟪∂ (p n) (uₙ t) (ⅆ (t':=t), uₙ t'), ∂ (p n) (uₙ t) v⟫ 
  --               = 
  --               ⟪f (p n (uₙ t)), ∂ (p n) (uₙ t) v⟫)
  --       ∧
  --       (∀ v, ⟪x₀ - p n (uₙ 0), ∂ (p n) (uₙ 0) v⟫ = 0))

  
  -- -- Give a fix approximation `p : U → X`, we form an approximation by 
  -- -- summing n copies of `p` i.e. `x` is approximated by `∑ i, p (u i)`
  -- def manifoldGalerkinNSolution {U} [Vec U] (f : X → X) (x₀ : X) (p : U → X) [IsSmooth p] (n : ℕ) :=
  --   let Uₙ := Fin n → U  -- U^n ???
  --   Solution (λ (uₙ : ℝ → Uₙ) => 
  --     (∀ i v t, (∑ j, ⟪∂ p (uₙ t j) (ⅆ uₙ t j), ∂ p (uₙ t i) v⟫) 
  --                = 
  --                ⟪f (∑ j, p (uₙ t j)), ∂ p (uₙ t i) v⟫)
  --     ∧ 
  --     ∀ i v, ⟪x₀ - (∑ j, p (uₙ 0 j)), ∂ p (uₙ 0 i) v⟫ = 0)

  noncomputable
  def massMatrixBlock {U} [Hilbert U] (p : U → X) (ui uj : U)
    : (U → U) := λ du => (λ v => ⟪∂ p uj du, ∂ p ui v⟫)† 1

  noncomputable
  def massMatrix {U} [Hilbert U] (p : U → X) {n : ℕ} (u du : Fin n → U) 
    : (Fin n → U) := λ i => ∑ j, massMatrixBlock p (u i) (u j) (du j) -- (λ v => ⟪∂ p (u j) (du j), ∂ p (u i) v⟫)† 1

  noncomputable
  def force {U} [Hilbert U] (f : X → X) (p : U → X) {n : ℕ} (u : Fin n → U) 
    : (Fin n → U) := λ i => (λ v => ⟪f (∑ j, p (u j)), ∂ p (u i) v⟫)† 1

  noncomputable
  def linForceBlock {U} [Hilbert U] (f : X → X) (p : U → X) {n : ℕ} (u : Fin n → U) 
    : (Fin n → Fin n → U) := λ i j => (λ v => ⟪f (p (u j)), ∂ p (u i) v⟫)† 1

  noncomputable
  def linForce {U} [Hilbert U] (f : X → X) (p : U → X) {n : ℕ} (u : Fin n → U) 
    : (Fin n → U) := λ i => ∑ j, linForceBlock f p u i j

  theorem force_linBlock {U} [Hilbert U] (f : X → X) (p : U → X) {n : ℕ} (u : Fin n → U) 
    : IsLin f → force f p u = linForce f p u := sorry

  noncomputable
  def blockJacobiStep {X} [Vec X] (A : Fin n → Fin n → X → X) (b : Fin n → X) (xₙ : Fin n → X) : Fin n → X :=
    λ i => (A i i)⁻¹ (b i - ∑ j, [[i≠j]] • A i j (xₙ j))

  -- def manifoldGalerkinImpl (p : U → X)
  --     (massMatrix : Approx λ u i j => massMatrixBlock p u i j)
  --     (diagMassInv : Approx λ u i => (massMatrix u i i)⁻¹)

  def Gaussian {X} [Hilbert X] (x : X) (σ : ℝ) := Real.exp (- (2*σ*σ)⁻¹ * ‖x‖²)

  
  theorem Gaussian.from_exp {X} [Hilbert X] (x : X) (α : ℝ) (h : α > 0)
    : Real.exp (-α * ‖x‖²)      
      =
      Gaussian x (Real.sqrt (2 * α))⁻¹
    := by simp; sorry -- simp[Gaussian] 

  function_properties AbstractManifolGalerkin.Gaussian {X} [Hilbert X] (x : X) (σ : ℝ)
  argument x
    IsSmooth,
    abbrev ∂ := λ dx => - (σ*σ)⁻¹ * ⟪dx, x⟫ * Gaussian x σ by sorry


  def GaussianDistrib {X} [Hilbert X] (x : X) (σ : ℝ) := 1 / (σ * Real.sqrt (2*Real.pi)) * Real.exp (- (2*σ*σ)⁻¹ * ‖x‖²)

  -- Nice pdf with bunch of formulas with gaussians: http://www.lucamartino.altervista.org/2003-003.pdf
  def Gaussian.product {X} [Hilbert X] (x μ₁ μ₂ : X) (σ₁ σ₂ : ℝ) :=
      let s2  := σ₁*σ₁ + σ₂*σ₂
      let w₁ := σ₂*σ₂ * s2⁻¹
      let w₂ := σ₁*σ₁ * s2⁻¹
      let μ₁₂ := w₁•μ₁ + w₂•μ₂
      let σ₁₂ := ((σ₁*σ₁) * (σ₂*σ₂) * s2⁻¹).sqrt
      let σ' := (σ₁*σ₂)/σ₁₂  -- √(σ₁^2 + σ₂^2)
      let S₁₂ := Gaussian (μ₁-μ₂) σ'
      S₁₂ * Gaussian (x - μ₁₂) σ₁₂

  theorem Gaussian.mul_product {X} [Hilbert X] (x μ₁ μ₂ : X) (σ₁ σ₂ : ℝ) 
    : Gaussian (x - μ₁) σ₁ * Gaussian (x - μ₂) σ₂
      =
      let s2  := σ₁*σ₁ + σ₂*σ₂
      let w₁ := σ₂*σ₂ * s2⁻¹
      let w₂ := σ₁*σ₁ * s2⁻¹
      let μ₁₂ := w₁•μ₁ + w₂•μ₂
      let σ₁₂ := ((σ₁*σ₁) * (σ₂*σ₂) * s2⁻¹).sqrt
      let σ' := (σ₁*σ₂)/σ₁₂  -- √(σ₁^2 + σ₂^2)
      let S₁₂ := Gaussian (μ₁-μ₂) σ'
      S₁₂ * Gaussian (x - μ₁₂) σ₁₂
    := sorry

  theorem GaussianDistrib.product {X} [Hilbert X] (x μ₁ μ₂ : X) (σ₁ σ₂ : ℝ) 
    : GaussianDistrib (x - μ₁) σ₁ * GaussianDistrib (x - μ₂) σ₂
      =
      let s2  := σ₁*σ₁ + σ₂*σ₂
      let w₁ := σ₂*σ₂ * s2⁻¹
      let w₂ := σ₁*σ₁ * s2⁻¹
      let μ₁₂ := w₁•μ₁ + w₂•μ₂
      let σ₁₂ := ((σ₁*σ₁) * (σ₂*σ₂) * s2⁻¹).sqrt
      let σ' := (σ₁*σ₂)/σ₁₂  -- √(σ₁^2 + σ₂^2)
      let S₁₂ := GaussianDistrib (μ₁-μ₂) σ'
      S₁₂ * GaussianDistrib (x - μ₁₂) σ₁₂
    := sorry

  theorem Gaussian.product_same_variance {X} [Hilbert X] (x μ₁ μ₂ : X) (σ : ℝ) 
    : Gaussian (x - μ₁) σ * Gaussian (x - μ₂) σ
      =
      let s2  := 2 * σ*σ
      let μ₁₂ := (1/2 : ℝ) • (μ₁ + μ₂)
      let σ₁₂ := σ / Real.sqrt 2 
      let σ' := Real.sqrt 2 * σ
      let S₁₂ := Gaussian (μ₁-μ₂) σ'
      S₁₂ * Gaussian (x - μ₁₂) σ₁₂
    := sorry

  theorem GaussianDistrib.product_same_variance {X} [Hilbert X] (x μ₁ μ₂ : X) (σ : ℝ) 
    : Gaussian (x - μ₁) σ * Gaussian (x - μ₂) σ
      =
      let s2  := 2 * σ*σ
      let μ₁₂ := (1/2 : ℝ) • (μ₁ + μ₂)
      let σ₁₂ := σ / Real.sqrt 2 
      let σ' := Real.sqrt 2 * σ
      let S₁₂ := GaussianDistrib (μ₁-μ₂) σ'
      S₁₂ * GaussianDistrib (x - μ₁₂) σ₁₂
    := sorry


  def Gaussian.complexify {X} [Hilbert X] (x : ComplexExtension X) (σ : ℝ) : ℂ :=
    let cnorm : ℂ := ⟨‖x.real‖² - ‖x.imag‖², 2*⟪x.real, x.imag⟫ ⟩
    Complex.exp (- (2*σ*σ)⁻¹ • cnorm )


  def Gaussian.complexify_to_real {X} [Hilbert X] (x : ComplexExtension X) (σ : ℝ) 
    : Gaussian.complexify x σ 
      =
      let θ := - (σ*σ)⁻¹ * ⟪x.real,x.imag⟫
      (Gaussian x.real σ / Gaussian x.imag σ) • ⟨Real.cos θ, Real.sin θ⟩ := 
  by
    simp [Gaussian.complexify, Complex.exp]
    -- this should be doable by simp + ring or something
    sorry


  theorem Gaussian.product_complex_exp {X} [Hilbert X] (x μ : X) (σ : ℝ) (k : X) (θ : ℝ) 
    : Gaussian (x - μ) σ • Complex.exp (⟨0, ⟪k,x⟫ + θ⟩)
      =
      Gaussian.complexify (⟨x - μ, (σ*σ)•k⟩) σ * Complex.exp ⟨- (σ*σ / 2) • ‖k‖², ⟪μ,k⟫ + θ⟩
    := sorry


  variable {ι} [Index ι] [FinVec X ι] (σ : ℝ) (Ω : Set X) (f : X → ℝ) (y : X)


  theorem integral_complex_shift [Hilbert R] (f : X → R) [IsAnalytic f] (y y' : X) 
    : ∃ (c : ℝ), ‖f x‖ ≤ c * (1 + ‖x‖^(2*Index.size ι)) -- some 
      → 
      ∫ x ∈ ⊤, complexify f ⟨x, y⟩
      =
      ((-1:ℝ)^(Index.size ι)) • ∫ x ∈ ⊤, complexify f ⟨x, y'⟩
    := sorry


    
  theorem cos_gaussian_to_complex (x k : X) (θ : ℝ)
    : complexify (λ x => f x * Real.cos (⟪k,x⟫ + θ) * Gaussian x σ)
      =
      λ ⟨x,y⟩ => complexify f ⟨x,y⟩ * (Complex.exp ⟨0, ⟪k,x⟫ + θ⟩ + Complex.exp ⟨⟪k,y⟫, - ⟪k,x⟫ - θ⟩) * Gaussian.complexify ⟨x,0⟩ σ
    := sorry


  #check (let a : Nat := 0;
          let b : Nat := 1
          a + b)
         rewrite_by
           conv =>
             enter [a,b]
             rw[add_comm]


  structure Params (X Y : Type) [Vec X] [Vec Y] where
    x : X
    k : X
    θ : ℝ
    a : Y
  deriving Vec

  function_properties AbstractManifolGalerkin.Params.x {X Y} [Vec X] [Vec Y] (p : Params X Y)
  argument p
    IsLin := sorry_proof,
    IsSmooth := sorry_proof,
    abbrev ∂ := λ dp => dp.x by sorry_proof

  function_properties AbstractManifolGalerkin.Params.k {X Y} [Vec X] [Vec Y] (p : Params X Y)
  argument p
    IsLin := sorry_proof,
    IsSmooth := sorry_proof,
    abbrev ∂ := λ dp => dp.k by sorry_proof

  function_properties AbstractManifolGalerkin.Params.θ {X Y} [Vec X] [Vec Y] (p : Params X Y)
  argument p
    IsLin := sorry_proof,
    IsSmooth := sorry_proof,
    abbrev ∂ := λ dp => dp.θ by sorry_proof

  function_properties AbstractManifolGalerkin.Params.a {X Y} [Vec X] [Vec Y] (p : Params X Y)
  argument p
    IsLin := sorry_proof,
    IsSmooth := sorry_proof,
    abbrev ∂ := λ dp => dp.a by sorry_proof

  instance [Hilbert X] [Hilbert Y] : Hilbert (Params X Y) := sorry

  #check HSMul

  def waveletParticle {X Y} [Hilbert X] [Hilbert Y] (σ : ℝ) (p : Params X Y) (x : X) : Y :=
    let x' := x-p.x
    (Real.cos (⟪x', p.k⟫ + p.θ) * Gaussian x' σ) • p.a

  function_properties AbstractManifolGalerkin.waveletParticle {X Y} [Hilbert X] [Hilbert Y] (σ : ℝ) (p : Params X Y)
  argument p
    IsSmooth,
    def ∂ by 
      unfold waveletParticle
      fun_trans only []
      fun_trans only []
      dsimp
      ring_nf

  #exit 
  theorem waveletParticle_complex_form {X} [Hilbert X] (σ : ℝ) (p : Params X) 
    : waveletParticle σ p 
      =
      ((waveletParticle σ p)
       rewrite_by
         unfold waveletParticle
         
         )
    := sorry
  
  variable {_ : EnumType ι} [FinVec X ι]

  noncomputable
  instance : Inner (X → ℝ) := ⟨λ f g => ∫ x ∈ ⊤, f x * g x⟩

  noncomputable
  instance : TestFunctions (X → ℝ) := sorry

  noncomputable
  instance : SemiHilbert (X → ℝ) := SemiHilbert.mkSorryProofs

  noncomputable
  instance : Hilbert (X → ℝ) := Hilbert.mkSorryProofs
  
  approx massMatrixBlockImpl (σ : ℝ) (pi pj : Params X) := massMatrixBlock (waveletParticle σ) pi pj
  by
    conv =>
      enter [1,dp]
      simp[massMatrixBlock]
      simp [Inner.inner]
      -- deal with the integral
      conv =>
        enter [1,v]
        simp [waveletParticle]
        fun_trans
        fun_trans
        fun_trans
        simp
    checkpoint
    conv =>
      enter [1,dp,1,v,1,x]
      ring_nf
 
end AbstractManifolGalerkin
