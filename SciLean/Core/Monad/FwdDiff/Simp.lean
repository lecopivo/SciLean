import SciLean.Core.Monad.FwdDiff.IsSmoothM

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 100000

namespace SciLean

variable {α β γ}
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
  rw[h]; --rw[compM.arg_x.fwdDiffM_simp]
  sorry
  -- done
  -- simp only [← compFDM_appFDM]
  -- apply FwdDiffMonad.fwdDiffM_comp f (λ x => (hf₂ x).1) g (λ x => (hg₂ x).1)
  -- done


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
  rw[← compM.arg_x.fwdDiffM_simp (hf₁ := by infer_instance) (hg₁ := _)] -- this is also odd
  simp
  sorry -- apply diagPairM.arg_x.isSmooth pure g   -- duh: why 'FwdDiffMonad m' can't be synthesized?

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
  -- rw[scombM.arg_x.fwdDiffM_simp]
  sorry


-- This prevents an infinite loop when using `scomb.arg_x.fwdDiffM_simp`  and `scombM.arg_x.fwdDiffM_simp`
-- @[simp ↓ low-2]
theorem scomb.arg_x.fwdDiffM_simp_safeguard (f : X → Y → m Z)
  : fwdDiffM (λ xy => f xy.1 xy.2) = fwdDiffM (Function.uncurry f) :=
by
  simp[Function.uncurry] done  


-- set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.simp.unify true in
example {W} [Vec W] (f : X → Y → m Z) 
  : fwdDiffM (λ x : ((W × Y) × X) => f x.2 x.1.2) 
    = 
    let Tf := fwdDiffM (λ ((x,y) : (X × Y)) => f x y)
    let g  := λ x : ((W × Y) × X) => (x.2,x.1.2)
    let Tg := mapFDM (m:=m) (fwdDiff g)
    λ x => (do appFDM Tf (← Tg x)) := 
by
  simp[mapFDM,appFDM]
  admit
  

