import SciLean.Core.Differential
import SciLean.Core.IsSmoothDep

namespace SciLean

variable {X Y Z W Y₁ Y₂ Y₃} [Diff X] [Diff Y] [Diff Z] [Diff W] [Diff Y₁] [Diff Y₂] [Diff Y₃]
  {α β γ : Type} 

noncomputable 
def differentialDep (f : X → Y) : (x : X) → 𝒯[x] X → 𝒯[f x] Y := sorry

noncomputable 
def tangentMapDep (f : X → Y) : 𝒯 X → 𝒯 Y := λ ⟨x,dx⟩ => ⟨f x, differentialDep f x dx⟩

noncomputable 
def tangentMapDep' (f : X → Y) (x : X) (dx : 𝒯[x] X) : (Σ' (y:Y) (dy : 𝒯[y] Y), (f x=y)) := ⟨f x, differentialDep f x dx, rfl⟩

instance(priority:=mid-1) (f : X → Y) : Partial f (differentialDep f) := ⟨⟩
instance(priority:=mid-1) (f : X → Y) : TangentMap f (tangentMapDep' f) := ⟨⟩


@[simp ↓]
theorem differentialDep.of_id
  : ∂ (λ x : X => x) = λ x dx => dx := sorry_proof

@[simp ↓]
theorem differentialDep.of_const (x : X)
  : ∂ (λ y : Y => x) = λ y dy => 0 := sorry_proof

@[simp ↓ low-3]
theorem differentialDep.of_swap (f : α → X → Y) [∀ i, IsSmoothDepT (f i)]
  : ∂ (λ x a => f a x) = λ x dx a => ∂ (f a) x dx := sorry_proof

@[simp ↓ low-1]
theorem differentialDep.of_comp
  (f : Y → Z) [IsSmoothDepT f]
  (g : X → Y) [IsSmoothDepT g]
  : ∂ (λ x => f (g x))
    =
    λ x dx =>
      -- option 1:
      let yy := 𝒯 g x dx
      let y := yy.1
      let dy := yy.2.1
      ∂ f y dy
      -- option 2:
      -- let y := g x
      -- let dy := ∂ g x dx
      -- have h : y = g x := by admit

      -- h ▸ ∂ f y dy
      -- option 3:
      -- ∂ f (g x) (∂ g x dx)
  := sorry_proof

@[simp ↓ low-2]
theorem differentialDep.of_diag
  (f : Y₁ → Y₂ → Z) [IsSmoothDepNT 2 f]
  (g₁ : X → Y₁) [IsSmoothDepT g₁]
  (g₂ : X → Y₂) [IsSmoothDepT g₂]
  : ∂ (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x dx => 
      let ⟨y₁,dy₁,h₁⟩ := 𝒯 g₁ x dx
      let ⟨y₂,dy₂,h₂⟩ := 𝒯 g₂ x dx 
      -- let y₁ := g₁ x
      -- let dy₁ := ∂ g₁ x dx
      -- let y₂ := g₂ x
      -- let dy₂ := ∂ g₂ x dx
      h₁ ▸ h₂ ▸ (∂ f y₁ dy₁ y₂ + ∂ (f y₁) y₂ dy₂)
  := sorry_proof


@[simp ↓ low-5]
theorem differentialDep.of_uncurryN (f : Y₁ → Y₂ → Z) [IsSmoothDepNT 2 f]
  : ∂ (uncurryN 2 f) 
    =
    λ (y₁,y₂) (dy₁,dy₂) =>
    ∂ f y₁ dy₁ y₂ + ∂ (f y₁) y₂ dy₂
  := by admit

@[simp ↓ low]
theorem differentialDep.of_parm
  (f : X → α → Y) [IsSmoothDepT f] (a : α)
  : ∂ (λ x => f x a) = λ x dx => ∂ f x dx a := 
by
  rw[differentialDep.of_swap (λ a x => f x a)]

@[simp ↓]
theorem differentialDep.of_eval
  (a : α)
  : ∂ (λ f : α → Y => f a) = λ _ df => df a := by simp

@[simp ↓]
theorem Prod.fst.arg_xy.diffDep_simp
  : ∂ (Prod.fst : X×Y → X) 
    =
    λ xy dxy => dxy.1
  := sorry_proof

@[simp ↓]
theorem Prod.snd.arg_xy.diffDep_simp
  : ∂ (Prod.snd : X×Y → Y) 
    =
    λ xy dxy => dxy.2
  := sorry_proof

--------------------------------------------------------------------------------
-- Tangent Map Rules --
--------------------------------------------------------------------------------

@[simp ↓]
theorem tangentMapDep.of_id
  : 𝒯 (λ x : X => x) = λ x dx => ⟨x,dx,rfl⟩
  := by simp[tangentMapDep']; done

@[simp ↓]
theorem tangentMapDep.of_const (x : X)
  : 𝒯 (λ y : Y => x) = λ y dy => ⟨x,0,rfl⟩
  := by simp[tangentMapDep']; done

@[simp ↓ low-3]
theorem tangentMapDep.of_swap (f : α → X → Y) [∀ i, IsSmoothDepT (f i)]
  : 𝒯 (λ x a => f a x) = λ x dx => ⟨λ a => f a x, λ a => ∂ (f a) x dx, rfl⟩
  := by simp[tangentMapDep']; done

@[simp ↓ low-1]
theorem tangentMapDep.of_comp
  (f : Y → Z) [IsSmoothDepT f]
  (g : X → Y) [IsSmoothDepT g]
  : 𝒯 (λ x => f (g x)) 
    = 
    λ x dx => 
      let ⟨y,dy,h⟩ := 𝒯 g x dx
      h ▸ 𝒯 f y dy
  := by simp[tangentMapDep']; done

@[simp ↓ low-2]
theorem tangentMapDep.of_diag
  (f : Y₁ → Y₂ → Z) [IsSmoothDepNT 2 f]
  (g₁ : X → Y₁) [IsSmoothDepT g₁]
  (g₂ : X → Y₂) [IsSmoothDepT g₂]
  : 𝒯 (λ x => f (g₁ x) (g₂ x))
    = 
    λ x dx => 
      let ⟨y₁,dy₁,h₁⟩ := 𝒯 g₁ x dx 
      let ⟨y₂,dy₂,h₂⟩ := 𝒯 g₂ x dx
      -- (f y₁ y₂, ∂ f y₁ dy₁ y₂ + ∂ (f y₁) y₂ dy₂)
      h₁ ▸ h₂ ▸ 𝒯 (uncurryN 2 f) (y₁,y₂) (dy₁,dy₂)
  := by 
    funext x dx
    simp[tangentMapDep']
    done



/-- Last resort theorem that changes tangent map to normal differential 

Bilinear maps should usually provide a rewrite rule for `𝒯 (uncurryN 2 f)`
-/
@[simp ↓ low-5]
theorem tangentMapDep.of_uncurryN (f : Y₁ → Y₂ → Z) [IsSmoothDepNT 2 f]
  : 𝒯 (uncurryN 2 f) 
    =
    λ  (y₁,y₂) (dy₁,dy₂) =>
    ⟨f y₁ y₂, ∂ f y₁ dy₁ y₂ + ∂ (f y₁) y₂ dy₂, rfl⟩
  := by 
    simp[tangentMapDep']
    done

@[simp ↓ low]
theorem tangentMapDep.of_parm
  (f : X → α → Y) [IsSmoothDepT f] (a : α)
  : 𝒯 (λ x => f x a) 
    = 
    λ x dx => 
      let ⟨f',df',h⟩ := 𝒯 f x dx
      ⟨f' a, df' a, by rw[h]; done⟩
  := by simp[tangentMapDep']; done

@[simp ↓]
theorem tangentMapDep.of_eval
  (a : α)
  : 𝒯 (λ f : α → Y => f a) 
    = 
    λ f df => 
      ⟨f a, df a, rfl⟩
  := by simp[tangentMapDep']; done

--------------------------------------------------------------------------------
