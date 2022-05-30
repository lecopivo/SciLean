import SciLean.Core.Monad.VecMonad

namespace SciLean

class IgnoreEffect (m : Type u → Type v) [Monad m] where
  ignoreEffect {α} : m α → m α

  bind_ignore_effect {α β} (ma : m α) (mb : m β) : 
    (bind (ignoreEffect ma) λ _ => mb) = mb

export IgnoreEffect (ignoreEffect)     

class DiffMonad (m : Type → Type) extends VecMonad m, IgnoreEffect m where
  IsSmoothM {X} [Vec X] (mx : m X) : Prop
  diffM     {X Y} [Vec X] [Vec Y] : (X → m Y) → m X → m X → m Y
  -- fwdDiffM  {X} [Vec X] : m X → m (X × (m X))

  dm  {X} [Vec X] : (m X) → (m Unit) → (m X)
  dm2 {X} [Vec X] : (m X) → m (m X)

  diffM_dm {X Y} [Vec X] [Vec Y] (f : X → m Y) [IsSmooth f] (hf : ∀ x, IsSmoothM (f x))
    : diffM f = λ mx mdx => do
        let dx ← (ignoreEffect mdx)
        let x  ← mx
        δ f x dx + (← ignoreEffect $ dm2 (f x))

  -- dm {X} [Vec X] : m X → m X
  -- dm {X Y} [Vec X] [Vec Y] : (X → m Y) → X → m (X → m Y)
  fwdDiffM {X Y} [Vec X] [Vec Y] : (X → m Y) → X → m (Y × (X → m Y))

  -- Possible variants of diffM
  -- diffM : (X → m Y) → X → m (X → m Y)
  -- diffM : (X → m Y) → X → m X → m (m Y)
  -- diffM : (X → m Y) → m X → m X → m (m Y)

  -- differentialM {X Y} [Vec X] [Vec Y] (f : X → m Y) (mx mdx : m X) : m (m Y) := do
  --   let x ← mx
  --   pureZero (do δ f x (← mdx)) + diffM (f x)

  -- diffM_fwdDiffM_fst {X} [Vec X] (mx : m X) : bind (fwdDiffM mx) (λ x => pure x.2) = diffM mx
  -- diffM_fwdDiffM_snd {X} [Vec X] (mx : m X) : bind (fwdDiffM mx) (λ x => pure x.1) = mx

  pure_isSmooth {X} [Vec X] : IsSmooth (Pure.pure : X → m X)
  pure_isSmoothM {X} [Vec X] (x : X) : IsSmoothM (pure x : m X)
  pure_diff_simp {X} [Vec X] : (δ λ x : X => pure x) = λ x dx => pureZero dx
  pure_diffM_simp {X} [Vec X] : (fwdDiffM λ x : X => pure x) = λ x => pure (x, λ dx => pureZero dx)

  -- pure_diffM_simp {X} [Vec X] (x : X) : (fwdDiffM (pure x : m X)) = pure (pure 0)

  bind_arg_x_isSmooth {X Y} [Vec X] [Vec Y] (f : X → m Y) [IsSmooth f] (hf : ∀ x, IsSmoothM (f x))
    : IsSmooth (λ mx => bind mx f)

  bind_arg_x_diff_simp {X Y} [Vec X] [Vec Y] (f : X → m Y) [IsSmooth f] (hf : ∀ x, IsSmoothM (f x))
    : δ (λ mx => bind mx f) = diffM  f
        -- let y ← fwdDiffM f (← mx)
        -- y.2 (← mdx)

  bind_arg_f_isSmooth {X Y} [Vec X] [Vec Y] (mx : m X) (hmx : IsSmoothM mx) : IsSmooth (bind mx : (X → m Y) → m Y)
  bind_isSmoothM {X Y} [Vec X] [Vec Y] (mx : m X) (hmx : IsSmoothM mx) 
    (f : X → m Y) [IsSmooth f] (hf : ∀ x, IsSmoothM (f x)) : IsSmoothM (bind mx f)
      -- λ mx mdx f => do 
      --   let x ← mx
      --   (← (pureZero (do δ f x (← mdx)) + (fwdDiffM (f x) >>= Prod.snd)))

  -- bind_arg_f_diff_simp {X Y} [Vec X] [Vec Y] (mx : m X) 
  --   : δ (bind mx : (X → m Y) → m Y)
  --     =
  --     λ f df => 
  --       bind mx df

  -- bind_diffM_simp {X Y} [Vec X] [Vec Y] (mx : m X) (hmx : IsSmoothM mx) 
  --   (f : X → m Y) [IsSmooth f] (hf : ∀ x, IsSmoothM (f x)) 
  --   : fwdDiffM (bind mx f) = do
  --        let (x,mdx) ← fwdDiffM mx  /- mdx holds dx and change of the state -/
  --        let mdfx ← fwdDiffM (f x)
  --        let mdf : m Y := (do δ f x (← mdx))
  --        pure (mdfx.1, mdfx.2 + mdf)


export DiffMonad (fwdDiffM IsSmoothM)

class IsSmoothM {m : Type → Type} [inst : DiffMonad m] {X} [Vec X] (x : m X) : Prop where
  isSmoothM : inst.IsSmoothM x

namespace DiffMonad

  attribute [simp] pure_diff_simp pure_diffM_simp bind_arg_x_diff_simp
  attribute [instance] pure_isSmooth pure_isSmoothM bind_arg_x_isSmooth

  -- example {m} [DiffMonad m] {X} [Vec X] [Vec Y] : IsSmooth (λ (mx : m X) (f : X → m Y) => bind mx f) := by infer_instance

  instance pureZero.arg_x.isSmooth {m} {X : Type} [Vec X] [inst : DiffMonad m] : IsSmooth (pureZero : X → m X) := 
  by
    have h : (pureZero : X → m X) = (δ pure 0) := by simp [inst.pure_diff_simp]
    rw [h]
    infer_instance

  -- Is this provable from current assumptions?
  instance pureZero.isSmoothM {m} {X : Type} [Vec X] [inst : DiffMonad m] (x : X) : IsSmoothM (pureZero x : m X) := 
  by
    have h : (pureZero : X → m X) = (δ pure 0) := by simp [inst.pure_diff_simp]
    rw [h];
    admit

  @[simp]
  theorem pureZero.arg_x.diff_simp {m} {X : Type} [Vec X] [inst : DiffMonad m] : δ (pureZero : X → m X) = λ x dx => pureZero dx := 
  by
    have h : (pureZero : X → m X) = (δ pure 0) := by simp [inst.pure_diff_simp]
    rw [h]
    apply diff_of_linear


section DifferentiableMonads

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 5000000

instance Id.instIgnoreEffect : IgnoreEffect Id where
  ignoreEffect := id
  bind_ignore_effect := by simp[ignoreEffect]

noncomputable
instance Id.instDiffMonad : DiffMonad Id where
  IsSmoothM (x) := True

  diffM := differential
  dm := λ x => 0
  dm2 := λ x => 0
  fwdDiffM f x := (f x, δ f x)

  diffM_dm := by intro X Y _ _ f _ _; simp[ignoreEffect]; rfl; done

  pure_isSmooth := by simp[pure] infer_instance
  pure_isSmoothM := by simp[pure]
  pure_diff_simp := by simp[pureZero]
  pure_diffM_simp := by simp[pureZero]

  bind_arg_x_isSmooth := by simp[bind]
  bind_arg_f_isSmooth := by simp[bind] infer_instance
  bind_isSmoothM := by simp[bind]
  bind_arg_x_diff_simp := by simp[bind]


-- theorem fooo {X Y} [Vec X] [Vec Y] : IsSmooth (λ (x : X) (y : Y) => (x, y)) := by infer_instance

-- set_option pp.funBinderTypes true in
-- set_option pp.notation false in
-- set_option trace.Meta.synthInstance true in
-- set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.simp.rewrite true in

instance StateM.instIgnoreEffect {σ} : IgnoreEffect (StateM σ) where
  ignoreEffect mx s := ((mx s).1, s)
  bind_ignore_effect := by simp[ignoreEffect, bind, StateT.bind]

noncomputable
instance StateM.instDiffMonad {σ} [Vec σ] : DiffMonad (StateM σ) where
  IsSmoothM (x) := IsSmooth x

  dm mx mu := λ s => δ mx s (mu s).2
  dm2 mx := λ s => (λ ds => δ mx s ds, (mx s).2) -- ((δ mx s ds), ds, s)

  diffM f mx mdx := λ s => 
    let (x, s')  := mx s
    let (dx, ds) := mdx s
    δ f x dx s' + δ (f x) s' ds

  diffM_dm := by 
    intro X Y _ _ f _ hf
    funext mx mdx s
    simp[bind, StateT.bind, pure, StateT.pure]
    simp[StateM,StateT,Id] at mx mdx f
    simp[fun_add_eval]; rfl
    done
    


  fwdDiffM f := λ x s => do
    -- let ((y, s'), dfds) ← fwdDiffM (f x) s
    let r ← fwdDiffM (f x) s
    pure ((r.1.1, λ dx ds => δ f x dx s + r.2 ds), s)

  pure_isSmooth := by simp[pure, StateT.pure]; intro X _; apply Prod.mk.arg_x.isSmooth
  -- pure_isSmoothM := by simp[pure]
  -- pure_diff_simp := by simp[pureZero]
  -- pure_diffM_simp := by simp[pureZero]

  bind_arg_x_isSmooth := sorry
  -- bind_arg_f_isSmooth := by simp[bind] infer_instance
  -- bind_isSmoothM := by simp[bind]
  bind_arg_x_diff_simp := by 
    simp[bind,StateT.bind, StateT, Id, StateM]
    intro X Y _ _ f _ hf
    funext mx mdx s
    simp done



-- set_option pp.notation false in
set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.rewrite true in
instance StateT.instDiffMonad [Vec σ] [DiffMonad m] : DiffMonad (StateT σ m) where
  IsSmoothM (x) := (IsSmooth λ s => x s) ∧ ∀ s, IsSmoothM (x s)

  -- diffM mx := λ s => do
  --   let ((x, s'), mdxs) ← fwdDiffM (mx s)
  --   pure (λ ds => δ mx s ds + mdxs, s') 

  fwdDiffM f := λ x s => do
      let ((y, s'), dfds) ← fwdDiffM (f x) s
      pure ((y, λ dx ds => dfds ds + δ f x dx s), s') /- should `δ f x dx s` contain s or s'? -/

    -- let ((y, s'), mdxs) ← fwdDiffM (f x)
    -- pure ((x, λ ds => δ f s ds + mdxs), s') 

  -- fdm {X Y} _ _ f x := 
  --   λ s => do
  --     let ((y, s'), dfds) ← fdm (f x) s
  --     pure ((y, λ dx ds => dfds ds + δ f x dx s), s') /- should `δ f x dx s` contain s or s'? -/
    
  -- diffM_fwdDiffM_fst (mx) := by 
  --   funext s
  --   simp[fwdDiffM, bind, StateT.bind, pure, StateT.pure, pureZero]
    
  -- diffM_fwdDiffM_snd (mx) := by 
  --   funext s
  --   simp[fwdDiffM, bind, StateT.bind, pure, StateT.pure]
  --   apply diffM_fwdDiffM_snd


  bind_arg_x_diff_simp := by
    intro X Y _ _
    simp[bind, StateT.bind, -bind_arg_x_diff_simp]
    funext mx mdx f s
    
    let dm : (X → m Y) → m X → m X → m (m Y) := λ f mx mdx => do        
      let x ← mx
      pureZero (do δ f x (← mdx)) + diffM (f x)
      
      
    admit
  -- vecM := λ X inst => by simp[StateT]; infer_instance
  -- pureZero := λ x s => pureZero (x, (0:σ))
  -- add_pureZero_right := by 
  --   intro X inst mx y; funext s
  --   simp[pure, StateT.pure, bind, StateT.bind] 
  --   rw[fun_add_eval]; simp [prod_add_elemwise]
  --   done
  -- bind_pureZero_pure := by
  --   intro X inst mx y; funext s
  --   simp[pure, StateT.pure, bind, StateT.bind]
  --   done



def squash {m} [Monad m] {α} (a : m (m α)) : m α := do
  let a' ← a
  a'
