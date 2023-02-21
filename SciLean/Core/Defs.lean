import SciLean.Data.Prod
import SciLean.Core.LinMap
import SciLean.Core.SmoothMap

namespace SciLean

open SciLean.Mathlib.Convenient

--- Definitions that need to be given upfroant

section OnPlainVectorSpaces

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z] 
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]


-- ∂ 

noncomputable 
opaque differential (f : X → Y) (x dx : X) : Y := 
  match Classical.propDecidable (is_smooth f) with
  | isTrue  h => Mathlib.Convenient.derivative f h x dx
  /- For nondifferentiable function the value is not specified.
     Maybe we could assign zero, similarly to division by zero.
     With zero, `differential` might be semilinear in `f`.
     This should be investigated! -/
  | _ => 0

noncomputable
def Smooth.differential (f : X ⟿ Y) : (X ⟿ X ⊸ Y) := 
  ⟨λ x => ⟨λ dx => SciLean.differential f.1 x dx, sorry_proof⟩, sorry_proof⟩

@[default_instance]
instance (f : X → Y) : Partial f (differential f) := ⟨⟩
instance (f : X ⟿ Y) : Partial f (Smooth.differential f) := ⟨⟩


-- ⅆ

noncomputable
def differentialScalar (f : ℝ → X) (t : ℝ) : X := 
  differential f t 1

noncomputable
def Smooth.differentialScalar (f : ℝ ⟿ X) : ℝ ⟿ X := 
  ⟨λ t => ((differential f t) 1), sorry_proof⟩

@[default_instance] 
instance differentialScalar.instDifferentialNotation (f : ℝ → X) 
  : Differential f (differentialScalar f) := ⟨⟩
instance Smooth.differentialScalar.instDifferentialNotation (f : ℝ ⟿ X) 
  : Differential f (Smooth.differentialScalar f) := ⟨⟩


-- 𝒯

noncomputable
def tangentMap (f : X → Y) : X×X → Y×Y := λ (x,dx) => (f x, ∂ f x dx)
noncomputable
def Smooth.tangentMap (f : X ⟿ Y) : X×X ⟿ Y×Y := ⟨λ (x,dx) => (f x, ∂ f x dx), sorry_proof⟩

@[default_instance]
instance (f : X → Y) : TangentMap f (tangentMap f) := ⟨⟩
instance (f : X ⟿ Y) : TangentMap f (Smooth.tangentMap f) := ⟨⟩


end OnPlainVectorSpaces

section OnSemiHilbertSpaces

variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] 
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]


-- †


noncomputable
def adjoint (f : X → Y) (y : Y) : X :=
  match Classical.propDecidable (has_adjoint f) with
  | isTrue h =>
    let f' := Classical.choose h.has_adjoint
    f' y
  | isFalse _ => 0
  
@[default_instance]
instance (f : X → Y) [SemiHilbert X] [SemiHilbert Y] : Dagger f (adjoint f) := ⟨⟩


-- ∂†

noncomputable 
def adjointDifferential (f : X → Y) (x : X) (dy' : Y) : X := (∂ f x)† dy'

@[default_instance]
instance (f : X → Y) : PartialDagger f (adjointDifferential f) := ⟨⟩


-- ℛ

noncomputable
def reverseDifferential (f : X → Y) (x : X) : Y×(Y→X) := (f x, λ dy => ∂† f x dy)

instance (priority:=low) (f : X → Y) : ReverseDifferential f (reverseDifferential f) := ⟨⟩


-- ∇

noncomputable
def gradient (f : X → ℝ) (x : X) : X := ∂† f x 1

noncomputable
def Smooth.gradient (f : X ⟿ ℝ) : X⟿X := SmoothMap.mk (λ x => adjoint (λ dx => ∂ f x dx) 1) sorry_proof


@[default_instance]
instance (f : X → ℝ) : Nabla f (gradient f) := ⟨⟩
instance (f : X ⟿ ℝ) : Nabla f (Smooth.gradient f) := ⟨⟩


end OnSemiHilbertSpaces
