import SciLean.Core.Monad.FwdDiff.IsSmoothM
import SciLean.Core.Monad.FwdDiff.Simp

set_option synthInstance.maxSize 2048
-- set_option synthInstance.maxHeartbeats 100000

namespace SciLean

noncomputable
instance {σ} [Vec σ] {m} [FwdDiffMonad m] : FwdDiffMonad (ReaderT σ m) where
  IsSmoothM mx := IsSmooth (λ s => mx s) ∧ ∀ s, SciLean.IsSmoothM (mx s)
  
  ---

  pure_is_smooth := by 
    simp[pure,ReaderT.pure,ReaderT,Id]; infer_instance done

  pure_is_smoothM x := by 
    simp[pure,ReaderT.pure,ReaderT,Id]; constructor; infer_instance; infer_instance done

  bind_is_smooth f hf₁ mhf₂ g hg₁ mhg₂ := by 
    simp[compM,bind,ReaderT.bind,pure,ReaderT.pure,ReaderT,Id] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
    have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x).1
    have hg₃ : ∀ x s, IsSmoothM (g x s) := λ x => (mhg₂ x).2
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y).1
    have hf₃ : ∀ x s, IsSmoothM (f x s) := λ x => (mhf₂ x).2
    infer_instance done

  bind_is_smoothM f hf₁ mhf₂ mx hx := by 
    simp[compM,bind,ReaderT.bind,pure,ReaderT.pure,ReaderT,Id,VecMonad] at f hf₁ mhf₂ mx hx ⊢
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y).1
    have hf₃ : ∀ x s, IsSmoothM (f x s) := λ x => (mhf₂ x).2

    -- For some reason these instances fail to be infered automatically 
    have hx1 : IsSmooth λ s => (mx s) := hx.1
    have hx2 : ∀ s, IsSmoothM (mx s) := hx.2

    constructor; infer_instance; infer_instance done

  diag_is_smooth f hf₁ mhf₂ g hg₁ mhg₂ := by
    simp[compM,bind,ReaderT.bind,pure,ReaderT.pure,ReaderT,Id] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
    have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x).1
    have hg₃ : ∀ x s, IsSmoothM (g x s) := λ x => (mhg₂ x).2
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y).1
    have hf₃ : ∀ x s, IsSmoothM (f x s) := λ x => (mhf₂ x).2
    infer_instance done

  diag_is_smoothM mx hx my hy := by
    simp[compM,bind,ReaderT.bind,pure,ReaderT.pure,ReaderT,Id] at mx hx my hy ⊢

    -- For some reason these instances fail to be infered automatically 
    have hx1 : IsSmooth λ s => (mx s) := hx.1
    have hx2 : ∀ s, IsSmoothM (mx s) := hx.2
    have hy1 : IsSmooth λ s => (my s) := hy.1
    have hy2 : ∀ s, IsSmoothM (my s) := hy.2

    constructor; infer_instance; infer_instance done
  
  ---

  fwdDiffM f := λ x s => do
     let (y,df) ← fwdDiffM (λ (x,s) => f x s) (x,s)
     pure (y, λ dx ds => df (dx,ds))

  fwdDiffM_id := by simp[pure,ReaderT.pure,ReaderT,Id,prod_add_elemwise,idFDM,idM,mapFDM,Function.uncurry]

  fwdDiffM_comp f hf₁ mhf₂ g hg₁ mhg₂ := by
    simp[fwdDiff,compM,compFDM,pure,ReaderT.pure,bind,ReaderT.bind,ReaderT,Id,prod_add_elemwise,fmaplrFDM,appFDM] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
    have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x).1
    have hg₃ : ∀ x s, IsSmoothM (g x s) := λ x => (mhg₂ x).2
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y).1
    have hf₃ : ∀ x s, IsSmoothM (f x s) := λ x => (mhf₂ x).2
    funext x s; simp; simp[appFDM,idFDM,fmaplrFDM, mapFDM]; unfold hold; simp[appFDM,idFDM,fmaplrFDM, mapFDM, fwdDiff]
    done

  ---

  mapFDM_id := by simp[pure,ReaderT.pure,idFD,idFDM,mapFDM]

  mapFDM_comp Tf Tg := by
    simp[bind,ReaderT.bind,pure,ReaderT.pure,idFD,idFDM,compFDM,compFD,mapFDM]

  ---

  fwdDiff_fwdDiffM f _ := by 
    simp[fwdDiff,pure,ReaderT.pure,ReaderT,Id,prod_add_elemwise,mapM]
    funext dx ds; simp[mapFDM,pure,ReaderT.pure]
    done

  const_fwdDiffM mx hx := by
    simp[fwdDiff,compM,compFDM,pure,ReaderT.pure,bind,ReaderT.bind,ReaderT,Id,prod_add_elemwise] at mx hx ⊢
    funext y s;
    have hx1 : IsSmooth λ s => (mx s) := hx.1
    have hx2 : ∀ s, IsSmoothM (mx s) := hx.2
    simp [diff_of_comp,mapFDM,appFDM]
    done

  diag_fwdDiffM f hf₁ mhf₂ g hg₁ mhg₂ := by
    simp[fwdDiff,compM,compFDM,pure,ReaderT.pure,bind,ReaderT.bind,ReaderT,Id,prod_add_elemwise,fmaplrFDM] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
    have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x).1
    have hg₃ : ∀ x s, IsSmoothM (g x s) := λ x => (mhg₂ x).2
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y).1
    have hf₃ : ∀ x s, IsSmoothM (f x s) := λ x => (mhf₂ x).2
    funext x s; 
    simp[idFDM, fmaplrFDM, appFDM, mapFDM, fwdDiff, prod_add_elemwise]
    done


