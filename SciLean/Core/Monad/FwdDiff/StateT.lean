import SciLean.Core.Monad.FwdDiff.IsSmoothM
import SciLean.Core.Monad.FwdDiff.Simp

set_option synthInstance.maxSize 2048
-- set_option synthInstance.maxHeartbeats 100000

namespace SciLean

example {X Y} [Vec X] [Vec Y] : fwdDiff (Prod.fst : X×Y→X) = λ xy => (xy.1, λ dxy => dxy.1) := by simp

-- set_option trace.Meta.Tactic.simp.rewrite true in
-- set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.simp.unify true in
noncomputable
instance {σ} [Vec σ] {m} [FwdDiffMonad m] : FwdDiffMonad (StateT σ m) where
  IsSmoothM mx := IsSmooth (λ s => mx s) ∧ ∀ s, SciLean.IsSmoothM (mx s)
  
  ---

  pure_is_smooth := by 
    simp[pure,StateT.pure,StateM,StateT,Id]; infer_instance done

  pure_is_smoothM x := by 
    simp[pure,StateT.pure,StateM,StateT,Id]; constructor; infer_instance; infer_instance done

  bind_is_smooth f hf₁ mhf₂ g hg₁ mhg₂ := by 
    simp[compM,bind,StateT.bind,pure,StateT.pure,StateM,StateT,Id] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
    have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x).1
    have hg₃ : ∀ x s, IsSmoothM (g x s) := λ x => (mhg₂ x).2
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y).1
    have hf₃ : ∀ x s, IsSmoothM (f x s) := λ x => (mhf₂ x).2
    infer_instance done

  bind_is_smoothM f hf₁ mhf₂ mx hx := by 
    simp[compM,bind,StateT.bind,pure,StateT.pure,StateM,StateT,Id,VecMonad] at f hf₁ mhf₂ mx hx ⊢
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y).1
    have hf₃ : ∀ x s, IsSmoothM (f x s) := λ x => (mhf₂ x).2

    -- For some reason these instances fail to be infered automatically 
    have hx1 : IsSmooth λ s => (mx s) := hx.1
    have hx2 : ∀ s, IsSmoothM (mx s) := hx.2

    constructor; infer_instance; infer_instance done

  diag_is_smooth f hf₁ mhf₂ g hg₁ mhg₂ := by
    simp[compM,bind,StateT.bind,pure,StateT.pure,StateM,StateT,Id] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
    have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x).1
    have hg₃ : ∀ x s, IsSmoothM (g x s) := λ x => (mhg₂ x).2
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y).1
    have hf₃ : ∀ x s, IsSmoothM (f x s) := λ x => (mhf₂ x).2
    infer_instance done

  diag_is_smoothM mx hx my hy := by
    simp[compM,bind,StateT.bind,pure,StateT.pure,StateM,StateT,Id] at mx hx my hy ⊢

    -- For some reason these instances fail to be infered automatically 
    have hx1 : IsSmooth λ s => (mx s) := hx.1
    have hx2 : ∀ s, IsSmoothM (mx s) := hx.2
    have hy1 : IsSmooth λ s => (my s) := hy.1
    have hy2 : ∀ s, IsSmoothM (my s) := hy.2

    constructor; infer_instance; infer_instance done
  
  ---

  fwdDiffM f := λ x s => do
     let ((y,s),df) ← fwdDiffM (λ (x,s) => f x s) (x,s)
     pure ((y, λ dx ds => df (dx,ds)), s)

  fwdDiffM_id := by simp[pure,StateT.pure,StateM,StateT,Id,prod_add_elemwise,idFDM,idM,Function.uncurry]

  fwdDiffM_comp f hf₁ mhf₂ g hg₁ mhg₂ := by
    simp[fwdDiff,compM,compFDM,pure,StateT.pure,bind,StateT.bind,StateT,StateM,Id,prod_add_elemwise,fmaplrFDM,appFDM] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
    have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x).1
    have hg₃ : ∀ x s, IsSmoothM (g x s) := λ x => (mhg₂ x).2
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y).1
    have hf₃ : ∀ x s, IsSmoothM (f x s) := λ x => (mhf₂ x).2
    funext x s; simp (config := {singlePass := true}); /- simp only [Prod.fst.arg_xy.fwdDiff_simp]; simp only [Prod.snd.arg_xy.fwdDiff_simp]; -/ simp (config := {singlePass := true}); simp (config := {singlePass := true}); simp (config := {singlePass := true}); simp[appFDM,Function.uncurry]
    done

  ---

  mapFDM_id := by simp[pure,StateT.pure,idFD,idFDM,mapFDM]

  mapFDM_comp Tf Tg := by
    simp[bind,StateT.bind,pure,StateT.pure,idFD,idFDM,compFDM,compFD,mapFDM]

  ---

  fwdDiff_fwdDiffM f _ := by 
    simp[fwdDiff,pure,StateT.pure,StateT,StateM,Id,prod_add_elemwise,mapM,Function.uncurry,mapFDM,appFD,hold]
    done

  const_fwdDiffM mx hx := by
    simp[fwdDiff,compM,compFDM,pure,StateT.pure,bind,StateT.bind,StateT,StateM,Id,prod_add_elemwise] at mx hx ⊢
    funext y s;
    have hx1 : IsSmooth λ s => (mx s) := hx.1
    have hx2 : ∀ s, IsSmoothM (mx s) := hx.2
    simp [diff_of_comp,mapFDM,appFDM]
    done

  diag_fwdDiffM f hf₁ mhf₂ g hg₁ mhg₂ := by
    simp[fwdDiff,compM,compFDM,pure,StateT.pure,bind,StateT.bind,StateT,StateM,Id,prod_add_elemwise,fmaplrFDM] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
    have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x).1
    have hg₃ : ∀ x s, IsSmoothM (g x s) := λ x => (mhg₂ x).2
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y).1
    have hf₃ : ∀ x s, IsSmoothM (f x s) := λ x => (mhf₂ x).2
    funext x s; 
    simp[idFDM, fmaplrFDM, appFDM, mapFDM, fwdDiff, prod_add_elemwise,appFD]; unfold hold
    simp[idFDM, fmaplrFDM, appFDM, mapFDM, fwdDiff, prod_add_elemwise,appFD]
    done



variable {X Y Z σ : Type} [Vec X] [Vec Y] [Vec Z] [Vec σ]
variable {m} [FwdDiffMonad m] 

instance StateT.run.isSmoothM (mx : StateT σ m X) [hx : IsSmoothM mx] : IsSmooth (StateT.run mx) := 
by
  simp[StateT.run]; apply hx.1.1; done

-- simp theorem for StateT.run ??

instance StateT.get.isSmoothM : IsSmoothM (get (m:=StateT σ m)) := 
by 
  simp[get,getThe,MonadStateOf.get,StateT.get]; constructor; simp[FwdDiffMonad.IsSmoothM]; constructor
  infer_instance; infer_instance
  done

@[simp ↓]
theorem StateT.get.fwdDiffM_simp 
  : fwdDiffM (λ _ : Unit => get (m:=StateT σ m)) 
    = 
    (fun y => do pure (← get, fun dy => get))
  := 
by
  simp[StateT.bind,bind,fwdDiffM,StateT.get,fwdDiff,get,getThe,MonadStateOf.get,pure,StateT.pure]; unfold hold; 
  simp[appFD,mapFDM,fwdDiff,prod_add_elemwise]; unfold hold; simp[prod_add_elemwise]; done

instance StateT.set.isSmooth : IsSmooth (λ s : σ => set (m:=StateT σ m) s) :=
by
  simp[StateT.set,set]; apply swap.arg_y.isSmooth -- infer_instance seems to fail :(

instance StateT.set.isSmoothM (s : σ) : IsSmoothM (set (m:=StateT σ m) s) :=
by
  simp[StateT.set,set]; 
  constructor; simp[FwdDiffMonad.IsSmoothM];
  constructor; infer_instance; infer_instance

@[simp ↓]
theorem StateT.set.fwdDiffM_simp
  : fwdDiffM (λ s : σ => set (m:= StateT σ m) s)
    =
    (λ s => do pure (← set s, λ ds => set ds))
  :=
by
  simp[fwdDiffM,StateT.set,fwdDiff,appFD,mapFDM,set,pure,StateT.pure,Zero.zero,OfNat.ofNat,bind,StateT.bind] 
  done

@[simp ↓]
theorem StateT.modify.fwdDiffM_simp (f : X → σ → σ) [IsSmooth f] [∀ x, IsSmooth (f x)]
  : fwdDiffM (λ x => modify (m:=StateT σ m) (f x))
    = 
    (λ x => do
      let s ← get
      let df := λ dx ds => ∂ f x dx s + ∂ (f x) s ds
      pure (← modify (f x), λ dx => modify (λ ds => df dx ds)))
  :=
by
  simp[fwdDiffM,modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,appFD,fwdDiff,mapFDM,set,bind,StateT.bind,pure,StateT.pure]; unfold hold;
  funext x s
  simp[get,getThe,MonadStateOf.get,StateT.get]
  done


