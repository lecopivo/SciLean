import SciLean.Core.AdjDiff
import SciLean.Core.AutoDiffSimps
import SciLean.AutoImpl

namespace SciLean

-- Neg --
------------------

instance Neg.neg.arg_x.isLin
  {X} [Vec X] 
  : IsLin (λ x : X => -x) := sorry_proof

instance Neg.neg.arg_x.isSmooth 
  {X} [Vec X] 
  : IsSmooth (λ x : X => -x) := by infer_instance

@[simp ↓, diff]
theorem Neg.neg.arg_x.diff_simp
  {X} [Vec X] 
  : ∂ (λ x : X => -x)
    =
    λ x dx => -dx := by simp

@[simp ↓, diff]
theorem Neg.neg.arg_x.tangentMap_simp
  {X} [Vec X] 
  : 𝒯 (λ x : X => -x)
    =
    λ (x,dx) => (-x, -dx) := by simp


instance Nat.neg.arg_x.hasAdjoint
  {X} [SemiHilbert X]
  : HasAdjoint (λ x : X => -x) := sorry_proof

@[simp ↓, diff]
theorem Neg.neg.arg_x.adjoint_simp
  {X} [SemiHilbert X] 
  : (λ x : X => -x)†
    =
    λ dy => -dy := sorry_proof

instance Neg.neg.arg_x.hasAdjDiff
  {X} [SemiHilbert X] 
  : HasAdjDiff (λ x : X => -x) := 
by apply infer_HasAdjDiff'; simp; infer_instance; done

@[simp ↓, diff]
theorem Neg.neg.arg_x.adjDiff_simp
  {X} [SemiHilbert X] 
  : ∂† (λ x : X => -x)
    =
    λ x dy => -dy := 
by
  simp[adjointDifferential]; done

@[simp ↓, diff]
theorem Neg.neg.arg_x.revDiff_simp
  {X} [SemiHilbert X] 
  : ℛ (λ x : X => -x)
    =
    λ x => (-x, λ dy => -dy) := 
by
  simp[reverseDifferential]; done


--------------------------------------------------------------------------------
-- Addition

-- argument (x,y) [SemiHilbert X]
--   hasAdjDiff
--   abbrev ∂† dxy := (dxy,dxy)
--   abbrev ℛ     -- auto

-- already exists
-- instance HAdd.hAdd.arg_xy.isSmooth
-- theorem HAdd.hAdd.arg_xy.diff_simp
-- theorem HAdd.hAdd.arg_xy.tangentMap_simp
-- instance HAdd.hAdd.arg_xy.hasAdjoint
-- theorem HAdd.hAdd.arg_xy.adjoint_simp
-- instance HAdd.hAdd.arg_xy.hasAdjDiff
-- theorem HAdd.hAdd.arg_xy.adjDiff_simp
-- theorem HAdd.hAdd.arg_xy.revDiff_simp

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
instance HAdd.hAdd.arg_x.isSmooth
  {X} [Vec X]
  : IsSmooth (λ (x y : X) => x + y) := by apply IsSmoothN.mk

@[simp ↓, diff]
theorem HAdd.hAdd.arg_x.diff_simp
  {X} [Vec X]
  : ∂ (λ (x y : X) => x + y) 
    = 
    λ x dx y => dx
  := by simp

@[simp ↓, diff]
theorem HAdd.hAdd.arg_x.tangentMap_simp
  {X} [Vec X]
  : 𝒯 (λ (x y : X) => x + y) 
    = 
    λ (x,dx) => (λ y => x+y, λ y => dx)
  := by simp[tangentMap]; done

instance HAdd.hAdd.arg_x.hasAdjDiff
  {X} [Hilbert X] (y : X)
  : HasAdjDiffT (λ (x : X) => x + y) := by apply infer_HasAdjDiff; simp; infer_instance; done

@[simp ↓, diff]
theorem HAdd.hAdd.arg_x.adjDiff_simp
  {X} [Hilbert X] (y : X)
  : ∂† (λ (x : X) => x + y)
    =
    λ x dz => dz
  := by unfold adjointDifferential; simp; done

@[simp ↓, diff]
theorem HAdd.hAdd.arg_x.revDiff_simp
  {X} [Hilbert X] (y : X)
  : ℛ (λ (x : X) => x + y)
    =
    λ x => (x + y, λ dx' : X => dx')
  := by unfold reverseDifferential; simp; done

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
instance HAdd.hAdd.arg_y.isSmooth
  {X} [Vec X] (x : X)
  : IsSmooth (λ (y : X) => x + y) := by apply IsSmoothN.mk

@[simp ↓,diff]
theorem HAdd.hAdd.arg_y.diff_simp
  {X} [Vec X] (x : X)
  : ∂ (λ (y : X) => x + y)
    =
    λ (y dy : X) => dy
  := by simp

@[simp ↓,diff]
theorem HAdd.hAdd.arg_y.tangentMap_simp
  {X} [Vec X] (x : X)
  : 𝒯 (λ (y : X) => x + y)
    =
    λ (y,dy) => (x + y, dy)
  := by simp[tangentMap]

instance HAdd.hAdd.arg_y.hasAdjDiff
  {X} [SemiHilbert X] (x : X)
  : HasAdjDiff (λ (y : X) => x + y) := sorry_proof

@[simp ↓, diff]
theorem HAdd.hAdd.arg_y.adjDiff_simp
  {X} [SemiHilbert X] (x : X)
  : ∂† (λ (y : X) => x + y)
    =
    λ (y dz : X) => dz
  := by simp[adjointDifferential]; done

@[simp ↓, diff]
theorem HAdd.hAdd.arg_y.revDiff_simp
  {X} [SemiHilbert X] (x : X)
  : ℛ (λ (y : X) => x + y)
    =
    λ y => (x + y, λ (dz : X) => dz)
  := by simp[reverseDifferential]; done


--------------------------------------------------------------------------------
-- Subtraction

-- argument (x,y) [SemiHilbert X]
--   hasAdjDiff
--   abbrev ∂† dxy := (dxy,dxy)
--   abbrev ℛ     -- auto

-- already exists
instance HSub.hSub.arg_xy.isLin
  {X} [Vec X]
  : IsLinN 2 (λ x y : X => x - y) := sorry_proof

instance HSub.hSub.arg_xy.isSmooth
  {X} [Vec X]
  : IsSmoothN 2 (λ x y : X => x - y) := by infer_instance

@[simp ↓, diff]
theorem HSub.hSub.arg_xy.diff_simp
  {X} [Vec X] 
  : ∂ (uncurryN 2 λ x y : X => x - y)
    =
    λ (x,y) (dx,dy) => dx - dy := by simp[uncurryN,Prod.Uncurry.uncurry]; done

@[simp ↓, diff]
theorem HSub.hSub.arg_xy.tangentMap_simp
  {X} [Vec X]
  : 𝒯 (uncurryN 2 λ x y : X => x - y)
    =
    λ ((x,y), (dx,dy)) => (x-y, dx-dy) := by simp[tangentMap]; done

instance HSub.hSub.arg_xy.hasAdjoint
  {X} [SemiHilbert X]
  : HasAdjoint (uncurryN 2 λ x y : X => x - y) := sorry_proof

@[simp ↓, diff]
theorem HSub.hSub.arg_xy.adjoint_simp
  {X} [SemiHilbert X]
  : (uncurryN 2 λ x y : X => x - y)†
    =
    λ z => (z,-z) := sorry_proof

instance HSub.hSub.arg_xy.hasAdjDiff
  {X} [SemiHilbert X]
  : HasAdjDiffN 2 (λ (x y : X) => x - y) := by apply infer_HasAdjDiff'; simp[uncurryN, Prod.Uncurry.uncurry]; infer_instance; done

@[simp ↓, diff]
theorem HSub.hSub.arg_xy.adjDiff_simp
  {X} [SemiHilbert X]
  : ∂† (uncurryN 2 λ (x y : X) => x - y)
    =
    λ (x,y) dxy => (dxy, -dxy)
  := by simp[uncurryN,Prod.Uncurry.uncurry,adjointDifferential,hold]; done

@[simp ↓, diff]
theorem HSub.hSub.arg_xy.revDiff_simp
  {X} [SemiHilbert X]
  : ℛ (uncurryN 2 λ (x y : X) => x - y) 
    =
    λ (x,y) => (x - y, λ dxy  => (dxy, -dxy))
  := by unfold reverseDifferential; simp; done


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
instance HSub.hSub.arg_x.isSmooth
  {X} [Vec X]
  : IsSmooth (λ (x y : X) => x - y) := by apply IsSmoothN.mk

@[simp ↓, diff]
theorem HSub.hSub.arg_x.diff_simp
  {X} [Vec X]
  : ∂ (λ (x y : X) => x - y) 
    = 
    λ x dx y => dx
  := by simp

@[simp ↓, diff]
theorem HSub.hSub.arg_x.tangentMap_simp
  {X} [Vec X]
  : 𝒯 (λ (x y : X) => x - y) 
    = 
    λ (x,dx) => (λ y => x-y, λ y => dx)
  := by simp[tangentMap]; done

instance HSub.hSub.arg_x.hasAdjDiff
  {X} [Hilbert X] (y : X)
  : HasAdjDiffT (λ (x : X) => x - y) := by apply infer_HasAdjDiff; simp; infer_instance; done

@[simp ↓, diff]
theorem HSub.hSub.arg_x.adjDiff_simp
  {X} [Hilbert X] (y : X)
  : ∂† (λ (x : X) => x - y)
    =
    λ x dz => dz
  := by unfold adjointDifferential; simp; done

@[simp ↓, diff]
theorem HSub.hSub.arg_x.revDiff_simp
  {X} [Hilbert X] (y : X)
  : ℛ (λ (x : X) => x - y)
    =
    λ x => (x - y, λ dx' : X => dx')
  := by unfold reverseDifferential; simp; done

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
instance HSub.hSub.arg_y.isSmooth
  {X} [Vec X] (x : X)
  : IsSmooth (λ (y : X) => x - y) := by apply IsSmoothN.mk

@[simp ↓,diff]
theorem HSub.hSub.arg_y.diff_simp
  {X} [Vec X] (x : X)
  : ∂ (λ (y : X) => x - y)
    =
    λ (y dy : X) => -dy
  := by simp

@[simp ↓,diff]
theorem HSub.hSub.arg_y.tangentMap_simp
  {X} [Vec X] (x : X)
  : 𝒯 (λ (y : X) => x - y)
    =
    λ (y,dy) => (x - y, -dy)
  := by simp[tangentMap]

instance HSub.hSub.arg_y.hasAdjDiff
  {X} [SemiHilbert X] (x : X)
  : HasAdjDiff (λ (y : X) => x - y) := sorry_proof

@[simp ↓, diff]
theorem HSub.hSub.arg_y.adjDiff_simp
  {X} [SemiHilbert X] (x : X)
  : ∂† (λ (y : X) => x - y)
    =
    λ (y dz : X) => -dz
  := by simp[adjointDifferential]; done

@[simp ↓, diff]
theorem HSub.hSub.arg_y.revDiff_simp
  {X} [SemiHilbert X] (x : X)
  : ℛ (λ (y : X) => x - y)
    =
    λ y => (x - y, λ (dz : X) => -dz)
  := by simp[reverseDifferential]; done



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

@[simp ↓, diff]
theorem HMul.hMul.arg_x.diff_simp
  {X} [Vec X]
  : ∂ (λ (x : ℝ) (y : X) => x * y) 
    = 
    λ x dx y => dx * y
  := by simp

@[simp ↓, diff]
theorem HMul.hMul.arg_x.tangentMap_simp
  {X} [Vec X]
  : 𝒯 (λ (x : ℝ) (y : X) => x * y) 
    = 
    λ (x,dx) => (λ y => x*y, λ y => dx*y)
  := by simp

instance HMul.hMul.arg_x.hasAdjoint
  {X} [Hilbert X] (y : X)
  : HasAdjoint (λ (x : ℝ) => x * y) := sorry_proof

@[simp ↓, diff]
theorem HMul.hMul.arg_x.hasAdjoint_simp
  {X} [Hilbert X] (y : X)
  : (λ (x : ℝ) => x * y)†
    = 
    λ x' => ⟪x',y⟫
  := sorry_proof

instance HMul.hMul.arg_x.hasAdjDiff
  {X} [Hilbert X] (y : X)
  : HasAdjDiffT (λ (x : ℝ) => x * y) := by apply infer_HasAdjDiff; simp; infer_instance; done

@[simp ↓, diff]
theorem HMul.hMul.arg_x.adjDiff_simp
  {X} [Hilbert X] (y : X)
  : ∂† (λ (x : ℝ) => x * y)
    =
    λ x dy => ⟪dy,y⟫
  := by unfold adjointDifferential; simp; done

@[simp ↓, diff]
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

@[simp ↓,diff]
theorem HMul.hMul.arg_y.diff_simp
  {X} [Vec X] (x : ℝ)
  : ∂ (λ (y : X) => x * y)
    =
    λ (y dy : X) => x * dy
  := by simp

@[simp ↓,diff]
theorem HMul.hMul.arg_y.tangentMap_simp
  {X} [Vec X] (x : ℝ)
  : 𝒯 (λ (y : X) => x * y)
    =
    λ (y,dy) => (x * y, x * dy)
  := by simp

instance HMul.hMul.arg_y.hasAdjoint
  {X} [SemiHilbert X] (x : ℝ)
  : HasAdjoint (λ (y : X) => x * y) := sorry_proof

@[simp ↓, diff]
theorem HMul.hMul.arg_y.adjoint_simp
  {X} [SemiHilbert X] (x : ℝ)
  : (λ (y : X) => x * y)†
    =
    λ (y' : X) => x * y'
  := sorry_proof

instance HMul.hMul.arg_y.hasAdjDiff
  {X} [SemiHilbert X] (x : ℝ)
  : HasAdjDiff (λ (y : X) => x * y) := sorry_proof

@[simp ↓, diff]
theorem HMul.hMul.arg_y.adjDiff_simp
  {X} [SemiHilbert X] (x : ℝ)
  : ∂† (λ (y : X) => x * y)
    =
    λ (y dy' : X) => x * dy'
  := by simp[adjointDifferential]; done

@[simp ↓, diff]
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

@[simp ↓, diff]
theorem HMul.hMul.arg_xy.diff_simp
  {X} [Vec X]
  : ∂ (uncurryN 2 λ (x : ℝ) (y : X) => x * y)
    = 
    λ (x,y) (dx,dy) =>
      dx * y + x * dy
  := by simp[uncurryN, Prod.Uncurry.uncurry]

@[simp ↓, diff]
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

@[simp ↓, diff]
theorem HMul.hMul.arg_xy.adjDiff_simp
  {X} [Hilbert X]
  : ∂† (uncurryN 2 λ (x : ℝ) (y : X) => x * y) 
    =
    λ (x,y) dxy => (⟪dxy,y⟫, x*dxy)
  := by simp[uncurryN,Prod.Uncurry.uncurry,adjointDifferential,hold]; 
        funext (x,y) dxy; simp
        admit

@[simp ↓, diff]
theorem HMul.hMul.arg_xy.revDiff_simp
  {X} [Hilbert X]
  : ℛ (uncurryN 2 λ (x : ℝ) (y : X) => x * y) 
    =
    λ (x,y) => (x*y, λ dxy => (⟪dxy,y⟫, x*dxy))
  := by unfold reverseDifferential; funext (x,y); simp; done


--------------------------------------------------------------------------------
-- Inner product

-- argument x

instance Inner.inner.arg_x.isLin
  {X} [Hilbert X]
  : IsLin (λ x y : X => ⟪x,y⟫) := sorry_proof

instance Inner.inner.arg_x.isSmooth
  {X} [Hilbert X]
  : IsSmooth (λ x y : X => ⟪x,y⟫) := by infer_instance

@[simp ↓, diff]
theorem Inner.inner.arg_x.diff_simp
  {X} [Hilbert X]
  : ∂ (λ x y : X => ⟪x,y⟫)
    =
    λ x dx y => ⟪dx,y⟫ := by simp

@[simp ↓, diff]
theorem Inner.inner.arg_x.tangentMap_simp
  {X} [Hilbert X]
  : 𝒯 (λ (x y : X) => ⟪x,y⟫)
    =
    λ (x,dx) => (λ y => ⟪x,y⟫, λ y => ⟪dx,y⟫) := by simp[tangentMap]


instance Inner.inner.arg_x.hasAdjoint
  {X} [Hilbert X] (y : X)
  : HasAdjoint (λ x : X => ⟪x,y⟫) := sorry_proof

@[simp ↓, diff]
theorem Inner.inner.arg_x.adjoint_simp
  {X} [Hilbert X] (y : X)
  : (λ x : X => ⟪x,y⟫)†
    =
    λ s => s * y := sorry_proof

instance Inner.inner.arg_x.hasAdjDiff
  {X} [Hilbert X] (y : X)
  : HasAdjDiff (λ x : X => ⟪x,y⟫) := by apply infer_HasAdjDiff'; simp[uncurryN, Prod.Uncurry.uncurry]; infer_instance; done

@[simp ↓, diff]
theorem Inner.inner.arg_x.adjDiff_simp
  {X} [Hilbert X] (y : X)
  : ∂† (λ x : X => ⟪x,y⟫)
    =
    λ x ds => ds * y := by unfold adjointDifferential; simp; done 

@[simp ↓, diff]
theorem Inner.inner.arg_x.revDiff_simp
  {X} [Hilbert X] (y : X)
  : ℛ (λ x : X => ⟪x,y⟫)
    =
    λ x => (⟪x,y⟫, λ ds => ds * y) := 
by 
  unfold reverseDifferential; 
  simp[reverseDifferential]
  done


-- argument y

instance Inner.inner.arg_y.isLin
  {X} [Hilbert X] (x : X)
  : IsLin (λ y : X => ⟪x,y⟫) := sorry_proof

instance Inner.inner.arg_y.isSmooth
  {X} [Hilbert X] (x : X)
  : IsSmooth (λ y : X => ⟪x,y⟫) := by infer_instance

@[simp ↓, diff]
theorem Inner.inner.arg_y.diff_simp
  {X} [Hilbert X] (x : X)
  : ∂ (λ y : X => ⟪x,y⟫)
    =
    λ y dy => ⟪x,dy⟫ := by simp

@[simp ↓, diff]
theorem Inner.inner.arg_y.tangentMap_simp
  {X} [Hilbert X] (x : X)
  : 𝒯 (λ y : X => ⟪x,y⟫)
    =
    λ (y,dy) => (⟪x,y⟫, ⟪x,dy⟫) := by simp

instance Inner.inner.arg_y.hasAdjoint
  {X} [Hilbert X] (x : X)
  : HasAdjoint (λ y : X => ⟪x,y⟫) := sorry_proof

@[simp ↓, diff]
theorem Inner.inner.arg_y.adjoint_simp
  {X} [Hilbert X] (x : X)
  : (λ y : X => ⟪x,y⟫)†
    =
    λ s => s * x := sorry_proof

instance Inner.inner.arg_y.hasAdjDiff
  {X} [Hilbert X] (x : X)
  : HasAdjDiff (λ y : X => ⟪x,y⟫) := by apply infer_HasAdjDiff'; simp[uncurryN, Prod.Uncurry.uncurry]; infer_instance; done

@[simp ↓, diff]
theorem Inner.inner.arg_y.adjDiff_simp
  {X} [Hilbert X] (x : X)
  : ∂† (λ y : X => ⟪x,y⟫)
    =
    λ y ds => ds * x := by simp[adjointDifferential,hold]; done

@[simp ↓, diff]
theorem Inner.inner.arg_y.revDiff_simp
  {X} [Hilbert X] (x : X)
  : ℛ (λ y : X => ⟪x,y⟫)
    =
    λ y => (⟪x,y⟫, λ ds => ds * x) := by simp[reverseDifferential,hold]; done


-- argument (x,y)

instance Inner.inner.arg_xy.isSmooth 
  {X} [Hilbert X] 
  : IsSmoothN 2 (λ x y : X => ⟪x,y⟫) := sorry_proof

@[simp ↓, diff]
theorem Inner.inner.arg_xy.diff_simp 
  {X} [Hilbert X] 
  : ∂ (uncurryN 2 λ x y : X => ⟪x,y⟫)
    =
    λ (x,y) (dx,dy) => ⟪dx,y⟫ + ⟪x,dy⟫ := by simp[uncurryN, Prod.Uncurry.uncurry]

@[simp ↓, diff]
theorem Inner.inner.arg_xy.tangentMap_simp 
  {X} [Hilbert X] 
  : 𝒯 (uncurryN 2 λ x y : X => ⟪x,y⟫)
    =
    λ ((x,y),(dx,dy)) => (⟪x,y⟫, ⟪dx,y⟫ + ⟪x,dy⟫) := by simp[tangentMap]

instance Inner.inner.arg_xy.hasAdjDiff 
  {X} [Hilbert X] 
  : HasAdjDiffN 2 (λ x y : X => ⟪x,y⟫) :=  by apply infer_HasAdjDiff'; simp[uncurryN, Prod.Uncurry.uncurry]; intro (x,y); infer_instance; done

@[simp ↓, diff]
theorem Inner.inner.arg_xy.ajdDiff_simp 
  {X} [Hilbert X]
  : ∂† (uncurryN 2 λ x y : X => ⟪x,y⟫)
    =
    λ (x,y) dz => (dz*y, dz*x) := by simp[adjointDifferential, uncurryN, Prod.Uncurry.uncurry, hold]; admit

@[simp ↓, diff]
theorem Inner.inner.arg_xy.revDiff_simp 
  {X} [Hilbert X]
  : ℛ (uncurryN 2 λ x y : X => ⟪x,y⟫)
    =
    λ (x,y) => (⟪x,y⟫, λ dz => (dz*y, dz*x)) := by simp[reverseDifferential]


-- Squared Norm --
------------------

instance Inner.normSqr.arg_x.isSmooth 
  {X} [Hilbert X] 
  : IsSmooth (λ x : X => ∥x∥²) := 
by
  unfold normSqr; apply IsSmoothN.mk; done

@[simp ↓, diff]
theorem Inner.normSqr.arg_x.diff_simp
  {X} [Hilbert X] 
  : ∂ (λ x : X => ∥x∥²)
    =
    λ x dx => 2*⟪dx,x⟫ := 
by
  unfold normSqr; simp; admit

@[simp ↓, diff]
theorem Inner.normSqr.arg_x.tangentMap_simp
  {X} [Hilbert X] 
  : 𝒯 (λ x : X => ∥x∥²)
    =
    λ (x,dx) => (∥x∥², 2*⟪dx,x⟫) := 
by
  simp[tangentMap]; done

instance Inner.normSqr.arg_x.hasAdjDiff
  {X} [Hilbert X] 
  : HasAdjDiff (λ x : X => ∥x∥²) := 
by apply infer_HasAdjDiff'; simp[uncurryN, Prod.Uncurry.uncurry]; infer_instance; done

@[simp ↓, diff]
theorem Inner.normSqr.arg_x.adjDiff_simp
  {X} [Hilbert X] 
  : ∂† (λ x : X => ∥x∥²)
    =
    λ x dy => 2*dy*x := 
by
  simp[adjointDifferential]; done

@[simp ↓, diff]
theorem Inner.normSqr.arg_x.revDiff_simp
  {X} [Hilbert X] 
  : ℛ (λ x : X => ∥x∥²)
    =
    λ x => (∥x∥², λ dy => 2*dy*x) := 
by
  simp[reverseDifferential]; done


--------------------------------------------------------------------------------
-- Pow

instance HPow.hPow.RealNatReal.arg_x.isSmooth (n : Nat)
  : IsSmooth (λ x : ℝ => x^n) := sorry_proof

@[simp ↓, diff]
theorem HPow.hPow.RealNatReal.arg_x.diff_simp (n : Nat)
  : ∂ (λ x : ℝ => x^n)
    =
    λ x dx : ℝ => n*dx*x^(n-1 : Nat)
  := sorry_proof

@[simp ↓, diff]
theorem HPow.hPow.RealNatReal.arg_x.tangentMap_simp (n : Nat)
  : 𝒯 (λ x : ℝ => x^n)
    =
    λ ((x,dx) : ℝ × ℝ) =>
      (x^n, n*dx*x^(n-1 : Nat))
  := by simp[tangentMap]; done

@[simp ↓, diff]
theorem HPow.hPow.RealNatReal.arg_x.HasAdjDiff (n : Nat)
  : HasAdjDiff (λ x : ℝ => x^n) :=
by apply infer_HasAdjDiff'; simp[uncurryN, Prod.Uncurry.uncurry]; infer_instance; done

@[simp ↓, diff]
theorem HPow.hPow.RealNatReal.arg_x.adjDiff_simp (n : Nat)
  : ∂† (λ x : ℝ => x^n)
    =
    λ x dy : ℝ => 
      n * dy * x^(n-1 : Nat)
  :=
by simp[adjointDifferential]; done

@[simp ↓, diff]
theorem HPow.hPow.RealNatReal.arg_x.reverseDiff_simp (n : Nat)
  : ℛ (λ x : ℝ => x^n)
    =
    λ x : ℝ => 
      (x^n, λ dy => n * dy * x^(n - 1 : Nat))
  :=
by simp[reverseDifferential]; done
 

--------------------------------------------------------------------------------
-- Differential 

instance differential.arg_fxdx.isSmooth 
  {X Y W} [Vec X] [Vec Y] [Vec W]
  (f : W → X → Y) [IsSmoothNT 2 f] : IsSmoothNT 3 (λ w x dx => ∂ (f w) x dx) := by (try infer_instance); sorry_proof

@[simp ↓, diff]
theorem differential.arg_f.diff_simp
  {X Y W} [Vec X] [Vec Y] [Vec W]
  (f : W → X → Y) [IsSmoothNT 2 f]
  : ∂ (λ w x dx => ∂ (f w) x dx)
    =
    λ w dw x dx =>
      ∂ (∂ f w dw) x dx
    := sorry_proof


-- already exists
-- instance differential.arg_dx.isLin

--------------------------------------------------------------------------------
-- Sum
--------------------------------------------------------------------------------

instance sum.arg_f.hasAdjoint {X ι} [Enumtype ι] [SemiHilbert X] 
  : HasAdjoint (sum : (ι → X) → X) := by (try infer_instance); sorry_proof
instance sum.arg_f.isLin {X ι} [Enumtype ι] [Vec X] 
  : IsLin (sum : (ι → X) → X) := by (try infer_instance); sorry_proof
instance sum.arg_f.isSmooth {X ι} [Enumtype ι] [Vec X] 
  : IsSmooth (sum : (ι → X) → X) := by infer_instance
instance sum.arg_f.hasAdjDiff {X ι} [Enumtype ι] [SemiHilbert X] 
  : HasAdjDiff (sum : (ι → X) → X) := by apply infer_HasAdjDiff'; symdiff; infer_instance; done

instance sum.arg_f.adj_simp {X ι} [Enumtype ι] [SemiHilbert X] 
  : (sum : (ι → X) → X)† = λ x i => x := sorry_proof

--------------------------------------------------------------------------------
-- Basis.proj
--------------------------------------------------------------------------------

instance Basis.proj.arg_x.hasAdjoint {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : HasAdjoint (λ x : X => 𝕡 i x) := by (try infer_instance); sorry_proof
instance Basis.proj.arg_x.isLin {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : IsLin (λ x : X => 𝕡 i x) := by infer_instance
instance Basis.proj.arg_x.isSmooth {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : IsSmooth (λ x : X => 𝕡 i x) := by infer_instance
instance Basis.proj.arg_x.hasAdjDiff {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : HasAdjDiff (λ x : X => 𝕡 i x) := by apply infer_HasAdjDiff'; symdiff; infer_instance; done

instance Basis.proj.arg_x.adj_simp {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : adjoint (λ (x : X) => 𝕡 i x) = (λ c => c * 𝕖'[X] i) := sorry_proof


--------------------------------------------------------------------------------
-- DualBasis.dualProj
--------------------------------------------------------------------------------

instance DualBasis.dualProj.arg_x.hasAdjoint {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : HasAdjoint (λ x : X => 𝕡' i x) := by (try infer_instance); sorry_proof
instance DualBasis.dualProj.arg_x.isLin {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : IsLin (λ x : X => 𝕡' i x) := by infer_instance
instance DualBasis.dualProj.arg_x.isSmooth {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : IsSmooth (λ x : X => 𝕡' i x) := by infer_instance
instance DualBasis.dualProj.arg_x.hasAdjDiff {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : HasAdjDiff (λ x : X => 𝕡' i x) := by apply infer_HasAdjDiff'; symdiff; infer_instance; done

instance DualBasis.dualProj.arg_x.adj_simp {X ι} [Enumtype ι] [FinVec X ι] (i : ι)
  : adjoint (λ (x : X) => 𝕡' i x) = (λ c => c * 𝕖[X] i) := sorry_proof
  


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
