import SciLean.Basic
import SciLean.Mechanics
import SciLean.Data.Prod
-- import SciLean.Solver.Solver

open SciLean

set_option synthInstance.maxSize 2048
-- set_option synthInstance.maxHeartbeats 5000000
-- set_option maxHeartbeats 5000000

variable {X : Type} [Hilbert X]

instance : IsSmooth Math.sin := sorry
instance : IsSmooth Math.cos := sorry
instance : IsSmooth Math.exp := sorry

@[simp]
theorem differential_of_cos : δ Math.cos = λ x dx => - dx * Math.sin x := sorry
@[simp]
theorem differential_of_sin : δ Math.sin = λ x dx => dx * Math.cos x := sorry
@[simp]
theorem differential_of_exp : δ Math.exp = λ x dx => dx * Math.exp x := sorry


instance : IsSmooth (λ (x : X×X) => ⟪x.1,x.1 + x.1⟫) := by infer_instance
instance : IsSmooth (λ ((r,s) : ℝ×ℝ) => r + r * r) := by simp; infer_instance

abbrev Parm (X : Type) [Hilbert X] {Y} [Hilbert Y] (P : Y ⟿ (X ⟿ ℝ)) := X × X × ℝ × Y

variable {Y: Type} [Hilbert Y] (P : Y ⟿ (X ⟿ ℝ)) 

instance : Hilbert (Parm X P) := by simp[Parm] infer_instance

def parm (r : ℝ) : Parm X P → (X → ℝ) := 
  λ (y,k,ω,α) => λ x => (P α x) * Math.cos (⟪k, x - y⟫ + ω) * Math.exp (- ∥x - y∥² * (1/r^2))

def parm' (r : ℝ) : Parm X P ⟿ (X ⟿ ℝ) := 
  ⟨λ (y,k,ω,α) => λ x ⟿ (P α x) * Math.cos (⟪k, x - y⟫ + ω) * Math.exp (- ∥x - y∥² * (1/r^2)), sorry⟩
  -- , by 
  --     simp;
  --     conv => 
  --       enter [1,x]
  --       simp[Smooth.Hom.mk]
  --     simp; infer_instance⟩


def parm'' (r : ℝ) : Parm X P → (X → ℝ) :=
  λ p => λ x =>
    let y := p[0]
    let k := p[1]
    let ω := p[2]
    let α := p[3]
    (P α x) * Math.cos (⟪k, x - y⟫ + ω) * Math.exp (- ∥x - y∥² * (1/r^2))
  -- , by simp infer_instance⟩
  -- , by simp infer_instance⟩

example (r : ℝ) : IsSmooth (λ α : Parm X P => parm'' P r α) := by simp[parm''] infer_instance

#check Subtype
@[simp] 
theorem differential_of_subtype {X : Type} [Vec X] (P : X → Prop) [Vec (Subtype P)] 
  : δ (λ x : (Subtype P) => x.1) = λ x dx => dx.1 := sorry

@[simp] 
theorem differential_of_fst {X Y : Type} [Vec X] [Vec Y] 
  : δ (λ ((x,y) : X×Y) => x) = λ (x,y) (dx,dy) => dx := sorry

@[simp] 
theorem differential_of_fst' {X Y : Type} [Vec X] [Vec Y] 
  : δ (λ (x : X×Y) => x.fst) = λ x dx => dx.fst := sorry

-- set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.simp.unify true in
noncomputable
example : Impl (δ λ p => parm'' P r p) := 
  by 
    -- funext (y,k,ω,α) (dy,dk,dω,dα)
    simp[parm'']
    unfold_atomic
    simp[Prod.getOp, Prod.Get.geti]
    unfold_atomic
    finish_impl


variable (x : ℂ) (y : ℝ)

constant integrall : (X → Y) → Y

prefix:max "∫" => integrall

#check SciLean.integral

variable [Hilbert X] {A : Type} [Hilbert A] [Hilbert Y]

variable (U : A → X → Y) [IsSmooth U] [∀ a, IsSmooth (U a)]

-- #check ∫ λ x : X => λ a b => λ da => (λ db => ⟪δ U a da x, δ U b db x⟫)† 1

variable (f : X → Y) (k : X) (ω r : ℝ)

-- #check (∫ λ x : X => ℂ.exp ⟨-∥x∥², ⟪k, x⟫⟩ * ⟨f x, 0⟩)
--        =
--        (∫ λ x : X => Math.exp (- ∥x∥²) * fᶜ ⟨x, -k⟩) -- Math.exp (- ∥x∥²) *



namespace AbstractManifolGalerkin

  structure ApproxSolution {X} [Vec X] (spec : X → Prop) where
    approx : ℕ → X
    proof : spec (limit val)

  structure Solution {X} [Vec X] (spec : X → Prop) where
    approx : X
    proof : spec val

  variable {X : Type} [Hilbert X]
  variable {U : ℕ → Type} [∀ n, Vec (U n)]

  variable (f : X → X) (x : ℝ → X)

  def manifoldGalerkinSolution (f : X → X) (x₀ : X) (p : (n : ℕ) → U n → X) [∀ n, IsSmooth (p n)] (n : ℕ) :=
    Solution (λ (uₙ : ℝ → U n) => 
        (∀ v t, ⟪ⅆ (p n ∘ uₙ) t, δ (p n) (uₙ t) v⟫ 
                = 
                ⟪f (p n (uₙ t)), δ (p n) (uₙ t) v⟫)
        ∧
        (∀ v, ⟪x₀ - p n (uₙ 0), δ (p n) (uₙ 0) v⟫ = 0))

  -- Give a fix approximation `p : U → X`, we form an approximation by 
  -- summing n copies of `p` i.e. `x` is approximated by `∑ i, p (u i)`
  def manifoldGalerkinNSolution {U} [Vec U] (f : X → X) (x₀ : X) (p : U → X) [IsSmooth p] (n : ℕ) :=
    let Uₙ := Fin n → U  -- U^n ???
    Solution (λ (uₙ : ℝ → Uₙ) => 
      (∀ i v t, (∑ j, ⟪δ p (uₙ t j) (ⅆ uₙ t j), δ p (uₙ t i) v⟫) 
                 = 
                 ⟪f (∑ j, p (uₙ t j)), δ p (uₙ t i) v⟫)
      ∧ 
      ∀ i v, ⟪x₀ - (∑ j, p (uₙ 0 j)), δ p (uₙ 0 i) v⟫ = 0)


  variable {U : Type} [Hilbert U] (f : X → X) (x₀ : X) (p : U → X) [IsSmooth p] (n : ℕ)

  -- Mass Matrix Block : U → U
  #check λ uj ui vj => (λ vi => ⟪δ p uj vj, δ p ui vi⟫)† 1

  -- rhs block for linear problems
  #check λ uj ui => (λ vi => ⟪f uj, δ p ui vi⟫)† 1

  #check Impl

  def manifoldGalerkinNSolution.blockwiseLinear {U} [Hilbert U] (f : X → X) (p : U → X) [IsSmooth p] (n : ℕ) (u₀ : Fin n → U) 
    (mblock : Impl (λ uj ui vj => (λ vi => ⟪δ p uj vj, δ p ui vi⟫)† 1))
    (fblock : Impl (λ uj ui => (λ vi => ⟪f (p uj), δ p ui vi⟫)† 1)) :=
    let Uₙ := Fin n → U  -- U^n ???
    let massMatrix : Uₙ → Uₙ → Uₙ := λ u v i => ∑ j, mblock.assemble! (u j) (u i) (v i)
    let forces : Uₙ → Uₙ := λ u i => ∑ j, fblock.assemble! (u j) (u i)
    Solution (λ (uₙ : ℝ → Uₙ) =>
      (∀ t, massMatrix (uₙ t) (ⅆ uₙ t) = forces (uₙ t))
      ∧
      (uₙ 0 = u₀))

  -- (ⅆ u = v) ∧ (ⅆ v = c^2 * Δ u)
  noncomputable
  def Δ {d : ℕ} (f : (ℝ^d) → ℝ) : (ℝ^d) → ℝ := sorry

  -- noncomputable
  -- def waveEquation (dim : ℕ) (speed : ℝ) : (ℝ → ℝ)×(ℝ → ℝ) → (ℝ → ℝ)×(ℝ → ℝ) := 
  --   λ (u, v) => (v, (speed^(2:ℝ)) * Δ u)


  /- position, wave vector, phase shift, amplitude -/
  abbrev 𝓤 := (ℝ^(2:ℕ)) × (ℝ^(2:ℕ)) × ℝ × ℝ

  def parm (r : ℝ) : 𝓤 → ((ℝ^(2:ℕ)) → ℝ) := 
    λ (y, k, ω, A) =>
    λ x => 
    A * Math.cos (⟪k, x - y⟫ - ω) *  Math.exp (- ∥x-y∥²/(r^2))

  /- Final flattened vector for speed -/
  abbrev Uₙ (n : ℕ) := ℝ^(n * 6)
  def elem  {n} : Uₙ n → (Fin n → 𝓤) := sorry
  def intro {n} : (Fin n → 𝓤) → Uₙ n := sorry

  def to_solution {n} : Uₙ n → (ℝ^(2:ℕ)) → ℝ := sorry

  /- The idea is that types `Z a` closely resonstruct the type `X` 
     However, this only works for well behaved elements in `X`, usuall smooth and/or integrable -/
  class ApproxSpace {N : Type} (Z : N → Type) (X : Type) where
    filter : Filter N
    canBeApproximated : X → Prop
    approx : 
      ∃ (interpolate : {n : N} → Z n → X) (sample : (n : N) → X → Z n), 
      (∀ n, sample n ∘ interpolate = id)
      ∧
      (∀ n (xₙ : Z n), canBeApproximated (interpolate xₙ))
      ∧
      (∀ x : X, canBeApproximated x → 
                lim filter (λ n => interpolate (sample n x)) = x)

  /- Sample -/
  class ToApproxSpace {N : Type} (Xₙ : N → Type) (X : Type) where
    toApproxSpace (n : N) : X → Xₙ n

  /- Interpolate -/
  class FromApproxSpace {N : Type} (Xₙ : N → Type) (X : Type) where
    fromApproxSpace {n} : Xₙ n → X
  
  instance [s : ApproxSpace Xₙ X] (α : Type) : ApproxSpace (λ n => α → Xₙ n) (α → X) := sorry
  instance [s : ApproxSpace Xₙ X] (α : Type) : ApproxSpace (λ n => Xₙ n → α) (X → α) := sorry
  instance [s : ApproxSpace Xₙ X] : ApproxSpace (λ n => Xₙ n → Xₙ n) (X → X) := sorry

  instance : ApproxSpace Uₙ ((ℝ^(2:ℕ)) → ℝ) := sorry

  -- impl asdf (x : ℝ) : X := ∇ Math.sin
  -- by
  --   asdf

  -- approx asdf (x : ℝ) : X := ∇ Math.sin
  -- by             
  --   asdf

  structure ApproxSol (Z : N → Type) {X : Type} (spec : X → Prop) [s : ApproxSpace Z X] where
    val : (n : N) → Z n
    -- proof : spec (lim s.filter (λ n => s.approx (val n)))

  class Foo (X : Type) where
    foo : X → X
    bar : X → X

  def real_noncomp (x : ℝ) : ℝ := x
  
  instance : Foo ℝ where
    foo x := 2 * x
    bar x := panic! "Implement me!"

  #eval (Foo.foo (2.0 : ℝ))
  #eval (Foo.bar (2.0 : ℝ))

  -- syntax declModifiers "def " declId bracketedBinder* (":" term)? ":=" term " rewrite " convSeq : command

  -- def adsf : ApproxT (λ n => ℝ → Uₙ n → Uₙ n) (ode_solve (waveEquation)) := sorry

  def ode_stepper (Xₙ : Nat → Type) (f : X → X) [ApproxSpace Xₙ X] 
  : ApproxSol (λ n => ℝ → Xₙ n → Xₙ n)
    (λ (ϕ : ℝ → X → X) => 
      ∀ x₀,
      let x := λ t => ϕ t x₀
      (∀ t, ⅆ x t = f (x t)) ∧ (x 0 = x₀)) := sorry

  
  -- def hihi : Impl (ode_solve (waveEquation 2 1.0)) :=
  -- by
  --   unfold waveEquation



    -- finish_impl

  -- theorem manifoldGalerkin (p : (n : ℕ) → U n → X) [∀ n, IsSmooth (p n)] (n : ℕ)
  --   : Solution (λ (uₙ : ℝ → U n) => 
  --       ∀ v t, ⟪ⅆ (p n ∘ uₙ) t, δ (p n) (uₙ t) v⟫ = ⟪f (p n (uₙ t)), δ (p n) (uₙ t) v⟫)
  --     → 
  --     ApproxSolution λ (x : ℝ → X) => ∀ t, ⅆ x t = f (x t)
  --   := sorry

  -- theorem manifoldGalerkinPaticles {U} [Vec U] (p : U → X) [IsSmooth p] (n : ℕ)
  --   : let Uₙ := Fin n → U
  --     let pₙ := λ (uₙ : Uₙ n) => ∑ i, uₙ i
  --     Solution (λ (uₙ : ℝ → Uₙ) => ∀ i t, )
  --     True
  --   := sorry

end AbstractManifolGalerkin
