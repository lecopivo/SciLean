import SciLean.NewStyle.IsLin
import SciLean.NewStyle.HasAdjoint

namespace SciLean

noncomputable
def adjoint {X Y} [SemiHilbert X] [SemiHilbert Y] 
    (f : X → Y) : Y → X 
    := sorry

postfix:max "†" => adjoint

theorem adjoint_is_linear {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) [HasAdjoint f] : IsLin (f†) := sorry

----------------------------------------------------------------------

variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι : Type} [Enumtype ι]

@[simp]
theorem id.arg_x.adj_simp
  : (λ x : X => x)† = λ x => x := sorry

@[simp]
theorem const.arg_x.adj_simp
  : (λ (x : X) (i : ι) => x)† = λ f => ∑ i, f i := sorry

@[simp]
theorem const.arg_y.adj_simp
  : (λ (y : Y) => (0 : X))† = λ y' => (0 : Y) := sorry

@[simp low]
theorem swap.arg_y.adj_simp
  (f : ι → Y → Z) [∀ i, HasAdjoint (f i)] 
  : (λ y i => f i y)† = λ g => ∑ i, (f i)† (g i) := sorry

@[simp low]
theorem comp.arg_x.adj_simp
  (f : Y → Z) [HasAdjoint f] 
  (g : X → Y) [HasAdjoint g] 
  : (λ x => f (g x))† = λ z => g† (f† z) := sorry

@[simp low]
theorem diag.arg_x.adj_simp
  (f : Y₁ → Y₂ → Z) [HasAdjoint (λ yy : Y₁ × Y₂ => f yy.1 yy.2)] 
  (g₁ : X → Y₁) [HasAdjoint g₁] 
  (g₂ : X → Y₂) [HasAdjoint g₂] 
  : (λ x => f (g₁ x) (g₂ x))† 
    = λ z => (λ (y₁,y₂) => (g₁† y₁) + (g₂† y₂)) $
             (λ (y₁,y₂) => f y₁ y₂)† z 
:= by sorry

-- This prevents an infinite loop when using `adjoint_of_diag` 
-- with `g₁ = Prod.fst` and `g₂ = Prod.snd`
@[simp low+1]
theorem diag.arg_x.adj_simp_safeguard
  (f : X → Y → Z) [HasAdjoint (λ ((x,y) : X×Y) => f x y)]
  : (λ (x,y) => f x y)† = (Function.uncurry f)† := 
by simp only [Function.uncurry] done

-- @[simp low]
-- theorem parm.arg_x.adj_simp
--   (f : X → ι → Z) [HasAdjoint f] (i : ι)
--   : (λ x => f x i)† = (λ z => f† (λ j => (kron i j) * z))
-- := sorry


----------------------------------------------------------------------
  -- These theorems are problematic when used with simp

def hold {α} (a : α) := a


@[simp low-1] -- try to avoid using this theorem
theorem comp.arg_x.parm1.adj_simp
  (a : α) 
  (f : Y → α → Z) [HasAdjoint (λ y => f y a)]
  (g : X → Y) [HasAdjoint g] 
  : 
    (λ x => f (g x) a)† = λ z => g† ((hold λ y => f y a)† z)
:= by 
  (apply comp.arg_x.adj_simp (λ y => f y a) g) done

example
  (a : α) 
  (f : Y → α → Z) [HasAdjoint (λ y => f y a)]
  (g : X → Y) [HasAdjoint g] 
  : 
    (λ x => f (g x) a)† = λ z => g† ((λ y => f y a)† z)
:= by simp

@[simp low-1] -- try to avoid using this theorem
theorem comp.arg_x.parm2.adj_simp
  (a : α) (b : β)
  (f : Y → α → β → Z) [HasAdjoint (λ y => f y a b)]
  (g : X → Y) [HasAdjoint g] 
  : 
    (λ x => f (g x) a b)† = λ z => g† ((hold λ y => f y a b)† z)
:= by 
  (apply comp.arg_x.adj_simp (λ y => f y a b) g) done

@[simp low-1] -- try to avoid using this theorem
theorem comp.arg_x.parm3.adj_simp
  (a : α) (b : β) (c : γ)
  (f : Y → α → β → γ → Z) [HasAdjoint (λ y => f y a b c)]
  (g : X → Y) [HasAdjoint g] 
  : 
    (λ x => f (g x) a b c)† = λ z => g† ((hold λ y => f y a b c)† z)
:= by 
  (apply comp.arg_x.adj_simp (λ y => f y a b c) g) done

-- theorem adjoint_of_comp_at_point4
-- ...

@[simp low-1] -- try to avoid using this theorem
theorem diag.arg_x.parm1.adj_simp
  (a : α)
  (f : Y₁ → Y₂ → α → Z) [HasAdjoint (λ (y₁,y₂) => f y₁ y₂ a)] 
  (g₁ : X → Y₁) [HasAdjoint g₁] 
  (g₂ : X → Y₂) [HasAdjoint g₂] 
  : (λ x => f (g₁ x) (g₂ x) a)† 
    = λ z => (λ (y₁,y₂) => (g₁† y₁) + (g₂† y₂)) $
             (hold λ (y₁,y₂) => f y₁ y₂ a)† z
:= by 
  (apply diag.arg_x.adj_simp (λ y₁ y₂ => f y₁ y₂ a) g₁ g₂) done

@[simp low-1] -- try to avoid using this theorem
theorem diag.arg_x.parm2.adj_simp
  (a : α) (b : β)
  (f : Y₁ → Y₂ → α → β → Z) [HasAdjoint (λ (y₁,y₂) => f y₁ y₂ a b)] 
  (g₁ : X → Y₁) [HasAdjoint g₁] 
  (g₂ : X → Y₂) [HasAdjoint g₂] 
  : (λ x => f (g₁ x) (g₂ x) a b)† 
    = λ z => (λ (y₁,y₂) => (g₁† y₁) + (g₂† y₂)) $
             (hold λ (y₁,y₂) => f y₁ y₂ a b)† z
:= by 
  (apply diag.arg_x.adj_simp (λ y₁ y₂ => f y₁ y₂ a b) g₁ g₂) done
