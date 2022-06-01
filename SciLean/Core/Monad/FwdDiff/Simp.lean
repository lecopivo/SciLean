import SciLean.Core.Monad.FwdDiff.IsSmoothM

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 100000

namespace SciLean

variable {α β γ}
variable {X Y Z Y₁ Y₂} [Vec X] [Vec Y] [Vec Z] [Vec Y₁] [Vec Y₂]
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


