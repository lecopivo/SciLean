import SciLean.Basic
import SciLean.Mechanics
import SciLean.Data.Prod

namespace SciLean

structure Complexify (X : Type) where
  re : X
  im : X
 
abbrev ℂ := Complexify ℝ
def 𝕚 : ℂ := ⟨0,1⟩

postfix:max "ᶜ" => Complexify

instance {X} [ToString X] : ToString Xᶜ := ⟨λ ⟨x,y⟩ => toString x ++ " + 𝕚 " ++ toString y⟩

variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

instance : Coe X Xᶜ := ⟨λ x => ⟨x,0⟩⟩

instance : Zero Xᶜ := ⟨⟨0,0⟩⟩
instance : Neg Xᶜ := ⟨λ ⟨x,y⟩ => ⟨-x,-y⟩⟩
instance : Add Xᶜ := ⟨λ ⟨x,y⟩ ⟨x',y'⟩ => ⟨x+x', y+y'⟩⟩
instance : Sub Xᶜ := ⟨λ ⟨x,y⟩ ⟨x',y'⟩ => ⟨x-x', y-y'⟩⟩
instance : HMul ℂ Xᶜ Xᶜ := ⟨λ ⟨a,b⟩ ⟨x,y⟩ => ⟨a * x - b * y, a * y + b * x⟩⟩
instance : HDiv Xᶜ ℂ Xᶜ :=
  ⟨λ ⟨x,y⟩ ⟨a,b⟩ =>
    let s : ℝ := 1/(a*a + b*b)
    ⟨s*(a*x - b*y), s*(b*x + a*y)⟩⟩

def Complexify.conj : Xᶜ → Xᶜ := λ ⟨x,y⟩ => ⟨x,-y⟩
@[simp]
theorem complex_conj_conj (x : Xᶜ) : x.conj.conj = x := by simp[Complexify.conj] done

-- These might be problematic
-- there might be multiple interpretations of x + y 
-- instance : HAdd X Xᶜ Xᶜ := ⟨λ x ⟨a,b⟩ => ⟨x + a, b⟩⟩
-- instance : HAdd Xᶜ X Xᶜ := ⟨λ ⟨a,b⟩ x => ⟨a + x, b⟩⟩
-- instance : HSub X Xᶜ Xᶜ := ⟨λ x ⟨a,b⟩ => ⟨x - a, -b⟩⟩
-- instance : HSub Xᶜ X Xᶜ := ⟨λ ⟨a,b⟩ x => ⟨a - x, b⟩⟩
-- instance : HMul ℂ X Xᶜ := ⟨λ r x => r * (x : Xᶜ)⟩
-- instance : HMul ℝ Xᶜ Xᶜ := ⟨λ r ⟨x,y⟩ => ⟨r * x, r * y⟩⟩

-- TODO: Fix me such that operations are well defined!
instance : Field ℂ := sorry
instance : Vec Xᶜ := sorry

--- (α → X)ᶜ = α → Xᶜ

constant complexify : (X → Y) → (Xᶜ → Yᶜ)

postfix:max "ᶜ" => complexify

def Taylor (f : X → Y) (n : Nat) (x₀ x : X) : Y := sorry

class Analytic {X Y} [Vec X] [Vec Y] (f : X → Y) where
  power_sum := ∀ x, f x = limit λ n => ∑ i : Fin n, Taylor f n 0 x

axiom complexify_id
  : (λ x : X => x)ᶜ = (λ x : Xᶜ => x)
axiom complexify_const (y : Y)
  : (λ x : X => y)ᶜ = (λ x : Xᶜ => (y : Yᶜ))
axiom complexify_comp
  (f : Y → Z) [Analytic f]
  (g : X → Y) [Analytic g]
  : (λ x : X => f (g x))ᶜ = (λ x : Xᶜ => fᶜ (gᶜ x))
axiom complexify_linear (f : X → Y) [IsLin f] 
  : fᶜ = λ ⟨x,y⟩ => ⟨f x, f y⟩

axiom complexify_add (f g : X → Y) [Analytic f] [Analytic g]
  : (λ x : X => f x + g x)ᶜ = (λ x : Xᶜ => fᶜ x + gᶜ x)
axiom complexify_mul (f : X → ℝ) (g : X → Y) [Analytic f] [Analytic g]
  : (λ x : X => f x * g x)ᶜ = (λ x : Xᶜ => fᶜ x * gᶜ x)
axiom complexify_inner [Hilbert Y] (f g : X → Y) [Analytic f] [Analytic g]
  : (λ x : X => ⟪f x, g x⟫)ᶜ
    = 
    λ x : Xᶜ => ⟨⟪(fᶜ x).re, (gᶜ x).re⟫ - ⟪(fᶜ x).im, (gᶜ x).im⟫,
                ⟪(fᶜ x).re, (gᶜ x).im⟫ + ⟪(fᶜ x).im, (gᶜ x).re⟫⟩

-- This should be derivable from some continuity of complexification
def ℂ.exp : ℂ → ℂ := λ ⟨x,y⟩ => Math.exp x * ⟨Math.cos y, Math.sin y⟩
abbrev Complex.exp := ℂ.exp
axiom complexify_exp : Math.expᶜ = ℂ.exp

