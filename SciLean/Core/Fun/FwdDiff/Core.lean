import SciLean.Core.Fun.Diff

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z] 
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

noncomputable 
def fwdDiff (f : X → Y) : X×X → Y×Y := λ (x,dx) => (f x, δ f x dx)

prefix:max "𝓣" => fwdDiff

def fwdDiff.split (f : α → β × γ) : (α → β)×(α→γ) := (λ a => (f a).1, λ a => (f a).2)
def fwdDiff.merge (fg : (α → β)×(α→γ)) : α → β×γ := λ a => (fg.1 a, fg.2 a) 
def fwdDiff.transpose : (Y₁×Y₁)×(Y₂×Y₂) → (Y₁×Y₂)×(Y₁×Y₂) := λ ((a,b),(c,d)) => ((a,c),(b,d))

theorem fwdDiff_of_linear (f : X → Y) [IsLin f] : 𝓣 f = λ (x,dx) => (f x, f dx) := 
by 
  simp [fwdDiff]
  rw[diff_of_linear]
  done

----------------------------------------------------------------------

@[simp, diff_core]
theorem id.arg_x.fwdDiff_simp
  : 𝓣 (λ x : X => x) = λ (x,dx) => (x,dx) := by simp[fwdDiff] done

@[simp, diff_core]
theorem const.arg_y.fwdDiff_simp (x : X)
  : 𝓣 (λ y : Y => x) = λ (y,dy) => (x,0) := by simp[fwdDiff] done

@[simp low-3]
theorem swap.arg_x.fwdDiff_simp (f : α → X → Y) [∀ i, IsSmooth (f i)]
  : 𝓣 (λ x a => f a x) = λ xdx => fwdDiff.split (λ a => 𝓣 (f a) xdx) := 
by 
  simp[fwdDiff, fwdDiff.split] done

@[simp low-1, diff_core low-1]
theorem comp.arg_x.fwdDiff_simp
  (f : Y → Z) [IsSmooth f] 
  (g : X → Y) [IsSmooth g] 
  : 𝓣 (λ x => f (g x)) = λ xdx => 𝓣 f (𝓣 g xdx) := by simp[fwdDiff] done

@[simp low-2, diff_core low-2]
theorem diag.arg_x.fwdDiff_simp
  (f : Y₁ → Y₂ → Z) [IsSmooth f] [∀ y₁, IsSmooth (f y₁)]
  (g₁ : X → Y₁) [IsSmooth g₁]
  (g₂ : X → Y₂) [IsSmooth g₂]
  : 𝓣 (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ xdx => 𝓣 (λ (y₁,y₂) => f y₁ y₂) (fwdDiff.transpose (𝓣 g₁ xdx, 𝓣 g₂ xdx))
  := 
  by
    funext x;
    simp[fwdDiff, fwdDiff.transpose, Function.comp]
    done

@[simp low, diff_core low]
theorem parm.arg_x.fwdDiff_simp
  (f : X → α → Y) [IsSmooth f] (a : α)
  : 𝓣 (λ x => f x a) = λ xdx => fwdDiff.merge (𝓣 f xdx) a := 
by 
  simp [fwdDiff.merge, fwdDiff] done


