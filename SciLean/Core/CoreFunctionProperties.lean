import SciLean.Core.AdjDiff
import SciLean.AutoImpl

namespace SciLean



--------------------------------------------------------------------------------
-- Multiplication

-- argument x * [Vec X]
--   isLin := sorry_proof
--   isSmooth
--   abbrev ∂ dx := dx * y
--   abbrev 𝒯 dx
-- argument x * [Hilbert X]
--   hasAdjoint := sorry_proof
--   abbrev † x' := ⟪x',y⟫
--   hasAdjDiff -- auto
--   abbrev ∂† dy := ⟪dy,y⟫
--   abbrev ℛ
instance HMul.hMul.arg_x.isLin
  {X} [Vec X]
  : IsLin (λ (x : ℝ) (y : X) => x * y) := sorry_proof

instance HMul.hMul.arg_x.isSmooth
  {X} [Vec X]
  : IsSmooth (λ (x : ℝ) (y : X) => x * y) := by infer_instance

@[simp, autodiff]
theorem HMul.hMul.arg_x.diff_simp
  {X} [Vec X]
  : ∂ (λ (x : ℝ) (y : X) => x * y) 
    = 
    λ x dx y => dx * y
  := by simp

@[simp, autodiff]
theorem HMul.hMul.arg_x.tangentMap_simp
  {X} [Vec X]
  : 𝒯 (λ (x : ℝ) (y : X) => x * y) 
    = 
    λ (x,dx) => (λ y => x*y, λ y => dx*y)
  := by simp

instance HMul.hMul.arg_x.hasAdjoint
  {X} [Hilbert X] (y : X)
  : HasAdjoint (λ (x : ℝ) => x * y) := sorry_proof

@[simp, autodiff]
theorem HMul.hMul.arg_x.hasAdjoint_simp
  {X} [Hilbert X] (y : X)
  : (λ (x : ℝ) => x * y)†
    = 
    λ x' => ⟪x',y⟫
  := sorry_proof

instance HMul.hMul.arg_x.hasAdjDiff
  {X} [Hilbert X] (y : X)
  : HasAdjDiffT (λ (x : ℝ) => x * y) := by apply infer_HasAdjDiff; simp; infer_instance; done

@[simp, autodiff]
theorem HMul.hMul.arg_x.adjDiff_simp
  {X} [Hilbert X] (y : X)
  : ∂† (λ (x : ℝ) => x * y)
    =
    λ x dy => ⟪dy,y⟫
  := by simp[adjointDifferential,hold]; done

@[simp, autodiff]
theorem HMul.hMul.arg_x.revDiff_simp
  {X} [Hilbert X] (y : X)
  : ℛ (λ (x : ℝ) => x * y)
    =
    λ x => (x * y, λ dy => ⟪dy,y⟫)
  := by unfold reverseDifferential; simp[hold]; done

-- argument y [Vec X]
--   isLin := sorry_proof
--   isSmooth      -- auto
--   abbrev ∂ dy := x * dy
--   abbrev 𝒯 dx  -- auto
-- argument y [Hilbert X]
--   hasAdjoint := sorry_proof
--   abbrev † y' := x*y'
--   hasAdjDiff -- auto
--   abbrev ∂† dy := x*dy
--   abbrev ℛ     -- auto
instance HMul.hMul.arg_y.isLin
  {X} [Vec X] (x : ℝ)
  : IsLin (λ (y : X) => x * y) := sorry_proof

instance HMul.hMul.arg_y.isSmooth
  {X} [Vec X] (x : ℝ)
  : IsSmoothT (λ (y : X) => x * y) := by infer_instance

@[simp,autodiff]
theorem HMul.hMul.arg_y.diff_simp
  {X} [Vec X] (x : ℝ)
  : ∂ (λ (y : X) => x * y)
    =
    λ (y dy : X) => x * dy
  := by simp

@[simp,autodiff]
theorem HMul.hMul.arg_y.tangentMap_simp
  {X} [Vec X] (x : ℝ)
  : 𝒯 (λ (y : X) => x * y)
    =
    λ (y,dy) => (x * y, x * dy)
  := by simp

instance HMul.hMul.arg_y.hasAdjoint
  {X} [SemiHilbert X] (x : ℝ)
  : HasAdjoint (λ (y : X) => x * y) := sorry_proof

@[simp, autodiff]
theorem HMul.hMul.arg_y.adjoint_simp
  {X} [SemiHilbert X] (x : ℝ)
  : (λ (y : X) => x * y)†
    =
    λ (y' : X) => x * y'
  := sorry_proof

instance HMul.hMul.arg_y.hasAdjDiff
  {X} [SemiHilbert X] (x : ℝ)
  : HasAdjDiff (λ (y : X) => x * y) := sorry_proof

@[simp, autodiff]
theorem HMul.hMul.arg_y.adjDiff_simp
  {X} [SemiHilbert X] (x : ℝ)
  : ∂† (λ (y : X) => x * y)
    =
    λ (y dy' : X) => x * dy'
  := by simp[adjointDifferential]; done

@[simp, autodiff]
theorem HMul.hMul.arg_y.revDiff_simp
  {X} [SemiHilbert X] (x : ℝ)
  : ℛ (λ (y : X) => x * y)
    =
    λ (y : X) => (x * y, λ (dy' : X) => x * dy')
  := by simp[reverseDifferential]; done


-- argument (x,y) [Vec X]
--   isSmooth := sorry_proof
--   abbrev ∂
--   abbrev 𝒯
-- argument (x,y) [Hilbert X]
--   hasAdjDiff
--   abbrev ∂† dy := x*dy
--   abbrev ℛ     -- auto

instance HMul.hMul.arg_xy.isSmooth
  {X} [Vec X]
  : IsSmoothN 2 (λ (x : ℝ) (y : X) => x * y) := sorry_proof

@[simp, autodiff]
theorem HMul.hMul.arg_xy.diff_simp
  {X} [Vec X]
  : ∂ (uncurryN 2 λ (x : ℝ) (y : X) => x * y)
    = 
    λ (x,y) (dx,dy) =>
      dx * y + x * dy
  := by simp[uncurryN, Prod.Uncurry.uncurry]

@[simp, autodiff]
theorem HMul.hMul.arg_xy.tangentMap_simp
  {X} [Vec X]
  : 𝒯 (uncurryN 2 λ (x : ℝ) (y : X) => x * y)
    = 
    λ ((x,y),(dx,dy)) =>
      (x*y, dx * y + x * dy)
  := by simp[uncurryN, Prod.Uncurry.uncurry]

instance HMul.hMul.arg_xy.hasAdjDiff
  {X} [Hilbert X]
  : HasAdjDiffN 2 (λ (x : ℝ) (y : X) => x * y) := by apply infer_HasAdjDiff'; simp[uncurryN, Prod.Uncurry.uncurry]; intro xy; infer_instance; done

@[simp, autodiff]
theorem HMul.hMul.arg_xy.adjDiff_simp
  {X} [Hilbert X]
  : ∂† (uncurryN 2 λ (x : ℝ) (y : X) => x * y) 
    =
    λ (x,y) dxy => (⟪dxy,y⟫, x*dxy)
  := by simp[uncurryN,Prod.Uncurry.uncurry,adjointDifferential,hold]; 
        funext (x,y) dxy; simp
        admit

@[simp, autodiff]
theorem HMul.hMul.arg_xy.revDiff_simp
  {X} [Hilbert X]
  : ℛ (uncurryN 2 λ (x : ℝ) (y : X) => x * y) 
    =
    λ (x,y) => (x*y, λ dxy => (⟪dxy,y⟫, x*dxy))
  := by unfold reverseDifferential; funext (x,y); simp; done



--------------------------------------------------------------------------------
-- Function.comp

instance Function.comp.arg_x.isSmooth
  {X Y Z} [Vec X] [Vec Y] [Vec Z] 
  (f : Y → Z) [IsSmoothT f]
  (g : X → Y) [IsSmoothT g] 
  : IsSmoothT (λ x => (f ∘ g) x) := by simp[Function.comp]; infer_instance; done

instance Function.comp.arg_x.isLin
  {X Y Z} [Vec X] [Vec Y] [Vec Z] 
  (f : Y → Z) [IsLinT f]
  (g : X → Y) [IsLinT g] 
  : IsLinT (λ x => (f ∘ g) x) := by simp[Function.comp]; infer_instance; done

instance Function.comp.arg_x.hasAdjoint
  {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] 
  (f : Y → Z) [HasAdjointT f]
  (g : X → Y) [HasAdjointT g] 
  : HasAdjointT (λ x => (f ∘ g) x) := by simp[Function.comp]; infer_instance; done

instance Function.comp.arg_x.hasAdjDiff
  {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] 
  (f : Y → Z) [HasAdjDiffT f]
  (g : X → Y) [HasAdjDiffT g] 
  : HasAdjDiffT (λ x => (f ∘ g) x) := by simp[Function.comp]; infer_instance; done


instance Function.comp.arg_g.isSmooth
  {α Y Z} [Vec Y] [Vec Z] 
  (f : Y → Z) [IsSmoothT f]
  : IsSmoothT (λ g : α → Y => f ∘ g) := by simp[Function.comp]; infer_instance; done


--------------------------------------------------------------------------------
