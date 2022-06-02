import SciLean.Core.Monad.FwdDiff.IsSmoothM

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 100000

namespace SciLean

variable {α β γ}
variable {X Y Z Y₁ Y₂ : Type} [Vec X] [Vec Y] [Vec Z] [Vec Y₁] [Vec Y₂]
variable {m} [FwdDiffMonad m]

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

theorem diagM.arg_x.fwdDiffM_simp
    (f : X → m Y) [hf₁ : IsSmooth f] [hf₂ : ∀ x, IsSmoothM (f x)]
    (g : X → m Z) [hg₁ : IsSmooth g] [hg₂ : ∀ x, IsSmoothM (g x)]
    : fwdDiffM (λ x => do pure (← f x, ← g x)) 
      = 
      fmaplrFDM (fwdDiffM f) (fwdDiffM g) :=
by
  apply FwdDiffMonad.diag_fwdDiffM f (λ x => (hf₂ x).1) g (λ x => (hg₂ x).1)
  done

-- set_option pp.all true in
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

