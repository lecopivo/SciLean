

import SciLean.Basic
import SciLean.Mechanics
import SciLean.Data.Prod

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

#check ∫ λ x : X => λ a b => λ da => (λ db => ⟪δ U a da x, δ U b db x⟫)† 1

variable (f : X → Y) (k : X) (ω r : ℝ)

#check (∫ λ x : X => ℂ.exp ⟨-∥x∥², ⟪k, x⟫⟩ * ⟨f x, 0⟩)
       =
       (∫ λ x : X => Math.exp (- ∥x∥²) * fᶜ ⟨x, -k⟩) -- Math.exp (- ∥x∥²) *
