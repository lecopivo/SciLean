import SciLean.Operators.Calculus.Differential
import SciLean.Operators.Adjoint

namespace SciLean.ReverseDiff

variable {α β γ α' β': Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {U V W : Type} [SemiHilbert U] [SemiHilbert V] [SemiHilbert W]
variable {V₁ V₂ : Type} [SemiHilbert V₁] [SemiHilbert V₂]
variable {ι κ : Type} [Enumtype ι] [Enumtype κ]

@[simp]
theorem reverse_diff_of_id
  : 𝓑 (λ x : U => x) = (λ x => (x, λ dx => dx)) :=
by 
  simp[reverse_diff] done

instance (x : U) : HasAdjoint (δ (λ x => x) x) := by simp infer_instance done

@[simp low]
theorem reverse_diff_of_swap
  (f : ι → U → V) [∀ i, IsSmooth (f i)] [∀ i x, HasAdjoint (δ (f i) x)]
  : 𝓑 (λ (x : U) (i : ι) => f i x) 
    = 
    λ x : U => (λ i : ι => f i x, 
                λ dg : ι → V => ∑ i, (𝓑 (f i) x).2 (dg i)) :=
by 
  simp[reverse_diff] done

instance (f : ι → U → V) [∀ i, IsSmooth (f i)] [∀ i x, HasAdjoint (δ (f i) x)] (x : U)
  : HasAdjoint (δ (λ x i => f i x) x) := by simp infer_instance done

@[simp]
theorem reverse_diff_of_const
  : 𝓑 (λ (x : U) (i : ι) => x) = λ x : U => (λ i : ι => x, λ f => sum f) :=
by 
  simp done

instance (x : U) : HasAdjoint (δ (λ (x : U) (i : ι) => x) x) 
  := by simp infer_instance done

@[simp low] 
theorem reverse_diff_of_comp 
  (f : V → W) [IsSmooth f] [∀ y, HasAdjoint (δ f y)]
  (g : U → V) [IsSmooth g] [∀ x, HasAdjoint (δ g x)]
  : 𝓑 (λ x => f (g x)) = (λ x => (𝓑 f • 𝓑 g) x) := 
by 
  funext x; simp[reverse_diff, reverse_diff, reverse_comp]
  funext dz; simp
  done

instance 
  (f : V → W) [IsSmooth f] [∀ y, HasAdjoint (δ f y)]
  (g : U → V) [IsSmooth g] [∀ x, HasAdjoint (δ g x)]
  (x : U)
  : HasAdjoint (δ (λ x => f (g x)) x) := by simp infer_instance done

-- abbrev or def? currently we keep only `reverse_comp`
abbrev reverse_lmap 
  (f : U → (V×(V→U))) 
  (g : U → (W×(W→U))) 
  : U → ((V×W)×(V×W → U)) 
:= 
  λ x =>
  let (fx, dfx) := f x
  let (gx, dgx) := g x
  ((fx, gx), λ (dy, dz) => dfx dy + dgx dz)

-- set_option trace.Meta.Tactic.simp.rewrite true in
-- set_option maxRecDepth 2048 in 
@[simp low]
theorem reverse_diff_of_diag
  (f : V₁ → V₂ → W) [IsSmooth f] [∀ y₂, IsSmooth (f y₂)] 
    [∀ y₁ y₂, HasAdjoint $ (λ dy₁ => δ f y₁ dy₁ y₂)]
    [∀ y₁ y₂, HasAdjoint $ (λ dy₂ => δ (f y₁) y₂ dy₂)]
  (g₁ : U → V₁) [IsSmooth g₁] [∀ x, HasAdjoint (δ g₁ x)]
  (g₂ : U → V₂) [IsSmooth g₂] [∀ x, HasAdjoint (δ g₂ x)]
  : 𝓑 (λ x => f (g₁ x) (g₂ x))
    = 
    𝓑 (Function.uncurry f) • reverse_lmap (𝓑 g₁) (𝓑 g₂) := 
by
  funext x; simp [reverse_diff, reverse_comp, Function.uncurry]
  funext dz; simp
  done

instance 
  (f : V₁ → V₂ → W) [IsSmooth f] [∀ y₂, IsSmooth (f y₂)] 
    [∀ y₁ y₂, HasAdjoint $ (λ dy₁ => δ f y₁ dy₁ y₂)]
    [∀ y₁ y₂, HasAdjoint $ (λ dy₂ => δ (f y₁) y₂ dy₂)]
  (g₁ : U → V₁) [IsSmooth g₁] [∀ x, HasAdjoint (δ g₁ x)]
  (g₂ : U → V₂) [IsSmooth g₂] [∀ x, HasAdjoint (δ g₂ x)]
  (x : U)
  : HasAdjoint (δ (λ x => f (g₁ x) (g₂ x)) x) := by simp infer_instance done
   
@[simp low] 
theorem reverse_diff_of_parm
  (f : U → ι → V) [IsSmooth f] [∀ x, HasAdjoint (δ f x)]
  (i : ι) 
  : 𝓑 (λ x => f x i) 
    = 
    (λ fx : ι → V => (fx i, λ dv j => kron i j * dv)) • 𝓑 f :=
    -- maybe this variant is better - which one produces better code?
    -- (λ x : U => (f x i, λ dv => (𝓑 f x).2 (λ j => kron i j * dv))) := 
by
  funext fx; simp [reverse_diff, reverse_comp]
  funext dv; simp
  done

instance
  (f : U → ι → V) [IsSmooth f] [∀ x, HasAdjoint (δ f x)]
  (i : ι) (x : U)
  : HasAdjoint (δ (λ x => f x i) x) := by simp infer_instance done
  
@[simp] 
theorem reverse_diff_of_function_comp
  (f : V → W) [IsSmooth f] [∀ y, HasAdjoint (δ f y)]
  (g : U → V) [IsSmooth g] [∀ x, HasAdjoint (δ g x)]
  : 𝓑 (f ∘ g) = (𝓑 f • 𝓑 g) :=
by
  simp[Function.comp] done

@[simp (low-1)] -- last resort
theorem reverse_diff_of_linear 
        (f : U → V) [IsLin f]
        (x : U)
        : 𝓑 f x = (f x, f†) := 
by 
  simp[reverse_diff] done
