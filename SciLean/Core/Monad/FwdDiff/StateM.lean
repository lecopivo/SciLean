/-
  This file serves mainly for educational purposes to demonstrate how 
  StateM is differentiable monad. For general case look at StateT.
 -/ 

import SciLean.Core.Monad.FwdDiff.Basic

set_option synthInstance.maxSize 2048
-- set_option synthInstance.maxHeartbeats 100000

namespace SciLean

noncomputable
instance {σ} [Vec σ] : FwdDiffMonad (StateM σ) where
  IsSmoothM mx := IsSmooth (λ s => mx s)
  
  ---

  pure_is_smooth := by 
    simp[pure,StateT.pure,StateM,StateT,Id]; infer_instance done
  pure_is_smoothM x := by 
    simp[pure,StateT.pure,StateM,StateT,Id]; infer_instance done

  bind_is_smooth f hf₁ mhf₂ g hg₁ mhg₂ := by 
    simp[compM,bind,StateT.bind,pure,StateT.pure,StateM,StateT,Id] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
    have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x)
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y)
    infer_instance done
  bind_is_smoothM f hf₁ mhf₂ mx hx := by 
    simp[compM,bind,StateT.bind,pure,StateT.pure,StateM,StateT,Id,VecMonad] at f hf₁ mhf₂ mx hx ⊢
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y)

    -- For some reason these instances fail to be infered automatically 
    have hx' : IsSmooth λ s => (mx s) := hx
    have hx₁ : IsSmooth λ s => (mx s).1 := by apply comp.arg_x.isSmooth
    have hx₂ : IsSmooth λ s => (mx s).2 := by apply comp.arg_x.isSmooth

    infer_instance done

  diag_is_smooth f hf₁ mhf₂ g hg₁ mhg₂ := by
    simp[compM,bind,StateT.bind,pure,StateT.pure,StateM,StateT,Id] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
    have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x)
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y)
    infer_instance done

  diag_is_smoothM mx hx my hy := by
    simp[compM,bind,StateT.bind,pure,StateT.pure,StateM,StateT,Id] at mx hx my hy ⊢

    -- For some reason these instances fail to be infered automatically 
    have hx' : IsSmooth λ s => (mx s) := hx
    have hx₁ : IsSmooth λ s => (mx s).1 := by apply comp.arg_x.isSmooth
    have hx₂ : IsSmooth λ s => (mx s).2 := by apply comp.arg_x.isSmooth
    have hy' : IsSmooth λ s => (my s) := hy
    have hy₁ : IsSmooth λ s => (my s).1 := by apply comp.arg_x.isSmooth
    have hy₂ : IsSmooth λ s => (my s).2 := by apply comp.arg_x.isSmooth

    infer_instance done
  
  ---

  fwdDiffM f := λ x s => 
     let ((y,s), df) := fwdDiff (λ (x,s) => f x s) (x,s)
     ((y, λ dx ds => df (dx,ds)), s)

  fwdDiffM_id := by simp[pure,StateT.pure,StateM,StateT,Id,prod_add_elemwise,idFDM,idM]

  fwdDiffM_comp f hf₁ mhf₂ g hg₁ mhg₂ := by
    simp[fwdDiff,compM,compFDM,pure,StateT.pure,bind,StateT.bind,StateT,StateM,Id,prod_add_elemwise,fmaplrFDM] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
    have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x)
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y)
    funext x s; simp
    done

  ---

  mapFDM_id := by simp[pure,StateT.pure,idFD,idFDM,mapFDM]

  mapFDM_comp Tf Tg := by 
    simp[bind,StateT.bind,pure,StateT.pure,idFD,idFDM,compFDM,compFD,mapFDM]

  ---

  fwdDiff_fwdDiffM f _ := by 
    simp[fwdDiff,pure,StateT.pure,StateT,StateM,Id,prod_add_elemwise,mapM,mapFDM]

  const_fwdDiffM mx hx := by
    simp[fwdDiff,compM,compFDM,pure,StateT.pure,bind,StateT.bind,StateT,StateM,Id,prod_add_elemwise] at mx hx ⊢
    funext y s;
    have hx' : IsSmooth λ s => (mx s) := hx
    simp [diff_of_comp]
    done

  diag_fwdDiffM f hf₁ mhf₂ g hg₁ mhg₂ := by
    simp[fwdDiff,compM,compFDM,pure,StateT.pure,bind,StateT.bind,StateT,StateM,Id,prod_add_elemwise,fmaplrFDM] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
    have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x)
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y)
    funext x s; simp[prod_add_elemwise]
    done
