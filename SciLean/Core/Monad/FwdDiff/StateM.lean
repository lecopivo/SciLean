import SciLean.Core.Functions

import SciLean.Core.Monad.VecMonad

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 100000

namespace SciLean

@[addPush]
theorem add_push_lin {X Y} [Vec X] [Vec Y] (f : X → Y) [IsLin f] (x x' : X)
  : f x + f x' = f (x + x') := sorry

@[addPull]
theorem add_pull_differential {X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f] (x dx dx' : X)
  : δ f x (dx + dx') = δ f x dx + δ f x dx' := sorry

@[addPull]
theorem add_pull_prod_fst {X Y} [Add X] [Add Y] (xy xy' : X×Y)
  : (xy + xy').1 = xy.1 + xy'.1 := sorry

@[addPull]
theorem add_pull_prod_snd {X Y} [Add X] [Add Y] (xy xy' : X×Y)
  : (xy + xy').2 = xy.2 + xy'.2 := sorry

noncomputable
instance {σ} [Vec σ] : FwdDiffMonad (StateM σ) where
  IsSmoothM mx := IsSmooth (λ s => mx s)
  
  fwdDiffM f := λ x s => 
     let ((y,s), df) := fwdDiff (λ (x,s) => f x s) (x,s)
     ((y, λ dx ds => df (dx,ds)), s)

  fwdDiffM_id := by simp[pure,StateT.pure,StateM,StateT,Id,prod_add_elemwise,idFDM,idM]

  fwdDiffM_comp f hf₁ mhf₂ g hg₁ mhg₂ := by
    simp[fwdDiff,compM,compFDM,pureZero, pure,StateT.pure,bind,StateT.bind,StateT,StateM,Id,prod_add_elemwise,uncurryFDM,fmaplrFDM] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
    have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x)
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y)
    funext x s; simp
    done

  mapFDM Tf := λ x s => 
    let (y,df) := Tf x
    ((y, λ dx ds => (df dx, ds)), s)

  mapFDM_id := by simp[pure,StateT.pure,idFD,idFDM]

  mapFDM_comp Tf Tg := by 
    simp[bind,StateT.bind,pure,StateT.pure,idFD,idFDM,compFDM,compFD]

  fwdDiff_fwdDiffM f _ := by 
    simp[fwdDiff,pure,StateT.pure,StateT,StateM,Id,prod_add_elemwise,mapM]

  fmap_fwdDiffM f hf₁ mhf₂ g hg₁ mhg₂ := by
    simp[fwdDiff,compM,compFDM,pureZero, pure,StateT.pure,bind,StateT.bind,StateT,StateM,Id,prod_add_elemwise,uncurryFDM,fmaplrFDM] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
    have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x)
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y)
    funext x s; simp[prod_add_elemwise]
    done
