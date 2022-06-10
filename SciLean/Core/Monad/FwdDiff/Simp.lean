import SciLean.Core.Monad.FwdDiff.IsSmoothM

set_option synthInstance.maxSize 20480
set_option synthInstance.maxHeartbeats 100000

namespace SciLean

variable {α β γ : Type}
variable {X Y Z Y₁ Y₂ : Type} [Vec X] [Vec Y] [Vec Z] [Vec Y₁] [Vec Y₂]
variable {m} [FwdDiffMonad m]

----------------------------------------------------------------------

@[simp ↓]
theorem fwdDiffM_pure_fwdDiff (f : X → Y) [IsSmooth f]
  : fwdDiffM (λ x => pure (f:=m) (f x)) = mapFDM (fwdDiff f) :=
by
  apply FwdDiffMonad.fwdDiff_fwdDiffM; done
  
----------------------------------------------------------------------

@[simp ↓]
theorem idM.arg_x.fwdDiffM_simp
  : fwdDiffM (λ x => (pure x : m X))
    =
    (λ x => pure (x, λ dx => pure dx)) :=
by
  apply FwdDiffMonad.fwdDiffM_id

@[simp ↓]
theorem constM.arg_x.fwdDiffM_simp (mx : m X) [hx : IsSmoothM mx]
  : fwdDiffM (λ y : Y => mx) = 
    (λ y => do
      let xdx ← fwdDiffM (hold λ _ : Unit => mx) ()
      pure (xdx.1, λ dy => xdx.2 ())) := 
by
  apply FwdDiffMonad.const_fwdDiffM mx hx.1

@[simp ↓ low]
theorem compM.arg_x.fwdDiffM_simp 
  (f : Y → m Z) [hf₁ : IsSmooth f] [hf₂ : ∀ y, IsSmoothM (f y)]
  (g : X → m Y) [hg₁ : IsSmooth g] [hg₂ : ∀ x, IsSmoothM (g x)]
  : fwdDiffM (λ x => g x >>= f) 
    = 
    λ x => fwdDiffM g x >>= appFDM (fwdDiffM f) :=
by 
  simp only [← compFDM_appFDM]
  apply FwdDiffMonad.fwdDiffM_comp f (λ x => (hf₂ x).1) g (λ x => (hg₂ x).1)
  done

@[simp ↓ low]
theorem comp.arg_x.fwdDiffM_simp 
  (f : Y → m Z) [hf₁ : IsSmooth f] [hf₂ : ∀ y, IsSmoothM (f y)]
  (g : X → Y) [hg₁ : IsSmooth g]
  : fwdDiffM (λ x => f (g x)) 
    = 
    (λ x => do
      let Tg := fwdDiff g
      let Tf := fwdDiffM f
      appFDM Tf (← mapFDM Tg x)) :=
by 
  have h : (λ x => f (g x)) = (λ x => (mapM g x) >>= f) := by simp[mapM]
  rw[h];
  rw[compM.arg_x.fwdDiffM_simp]
  simp[mapM,mapFDM]
  done

theorem diagM.arg_x.fwdDiffM_simp
    (f : X → m Y) [hf₁ : IsSmooth f] [hf₂ : ∀ x, IsSmoothM (f x)]
    (g : X → m Z) [hg₁ : IsSmooth g] [hg₂ : ∀ x, IsSmoothM (g x)]
    : fwdDiffM (λ x => do pure (← f x, ← g x)) 
      = 
      fmaplrFDM (fwdDiffM f) (fwdDiffM g) :=
by
  apply FwdDiffMonad.diag_fwdDiffM f (λ x => (hf₂ x).1) g (λ x => (hg₂ x).1)
  done

@[simp ↓ low-3]
theorem scombM.arg_x.fwdDiffM_simp
  (f : X → Y → m Z) [IsSmooth f] [∀ x, IsSmooth (f x)] [∀ x y, IsSmoothM (f x y)]
  (g : X → m Y) [IsSmooth g] [∀ x, IsSmoothM (g x)]
  : fwdDiffM (λ x => (do f x (← g x) : m Z)) 
    =
    (λ x => do
      let Tg := fwdDiffM g
      let Tf := fwdDiffM (λ xy => f xy.1 xy.2)
      fmaplrFDM idFDM Tg x >>= appFDM Tf) := 
by
  rw[← FwdDiffMonad.fwdDiffM_id]
  simp only[← diagM.arg_x.fwdDiffM_simp, idM]
  rw[← compM.arg_x.fwdDiffM_simp]
  simp [-compM.arg_x.fwdDiffM_simp]
  done

-- @[simp ↓ low-3]
theorem scomb.arg_x.fwdDiffM_simp
  (f : X → Y → m Z) [IsSmooth f] [∀ x, IsSmooth (f x)] [∀ x y, IsSmoothM (f x y)]
  (g : X → Y) [IsSmooth g]
  : fwdDiffM (λ x => (do f x (g x) : m Z)) 
    =
    (λ x => do
      let Tg := fwdDiff g
      let Tf := fwdDiffM (hold λ xy => f xy.1 xy.2)
      fmaplrFDM idFDM (mapFDM Tg) x >>= appFDM Tf) := 
by
  have h : (λ x => (do f x (g x) : m Z)) = (λ x => (do f x (← (mapM g) x) : m Z)) := by simp[mapM]
  rw[h]
  rw[scombM.arg_x.fwdDiffM_simp]
  sorry

-- set_option pp.all true in
-- set_option trace.Meta.synthInstance true in
@[simp ↓ low-1]
theorem diag.arg_x.fwdDiffM_simp
  (f : Y₁ → Y₂ → m Z) [IsSmooth f] [∀ y₁, IsSmooth (f y₁)] [∀ y₁ y₂, IsSmoothM (f y₁ y₂)]
  (g₁ : X → Y₁) [IsSmooth g₁]
  (g₂ : X → Y₂) [IsSmooth g₂]
  : fwdDiffM (λ x => (do f (g₁ x) (g₂ x) : m Z)) 
    =
    -- (λ x => do
    --   let Tg₁ := fwdDiff g₁
    --   let Tg₂ := fwdDiff g₂
    --   let Tf := fwdDiffM (hold λ y => f y.1 y.2)
    --   fmaplrFDM (mapFDM Tg₁) (mapFDM Tg₂) x >>= appFDM Tf) := 
    (λ x => do
      let (y₁, dy₁) := fwdDiff g₁ x
      let (y₂, dy₂) := fwdDiff g₂ x
      let Tf := fwdDiffM (hold λ y => f y.1 y.2)
      appFDM Tf ((y₁,y₂), λ dx => pure (dy₁ dx, dy₂ dx))) := 

by
  have h : (λ x => (do f (g₁ x) (g₂ x) : m Z))
            = 
            (λ x => (g₁ x, g₂ x) |> (λ y => f y.1 y.2)) := by simp[mapM]
  rw[h]
  conv => lhs; rw[comp.arg_x.fwdDiffM_simp (λ y => f y.1 y.2) (λ x => (g₁ x, g₂ x))]
  funext x
  simp[fmaplrFDM, mapFDM, appFDM, idFDM, mapM, fwdDiff,prod_add_elemwise,hold]
  done

  

