import SciLean.Analysis.Calculus.Monad.FwdFDerivMonad
import SciLean.Analysis.Calculus.Monad.RevFDerivMonad

namespace SciLean


section FwdFDerivMonad


variable
  {K : Type} [RCLike K]
  {m : Type → Type} {m' : outParam $ Type → Type} [Monad m] [Monad m']
  [DifferentiableMonad K m] [FwdFDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']

noncomputable
instance (S : Type) [NormedAddCommGroup S] [NormedSpace K S] :
    DifferentiableMonad K (StateT S m) where

  DifferentiableM f := DifferentiableM K (fun (xs : _×S) => f xs.1 xs.2)

  DifferentiableM_pure f hf :=
    by
      simp [Pure.pure,StateT.pure]
      fun_prop

  DifferentiableM_bind f g hf hg :=
    by
      simp[bind, StateT.bind]
      fun_prop

  DifferentiableM_pair f hf :=
    by
      simp[bind, StateT.bind, pure, StateT.pure, Functor.map]
      fun_prop


noncomputable
instance (S : Type) [NormedAddCommGroup S] [NormedSpace K S] :
    FwdFDerivMonad K (StateT S m) (StateT (S×S) m') where
  fwdFDerivM f := fun x dx sds => do
    -- ((y,s'),(dy,ds'))
    let r ← fwdFDerivM K (fun (xs : _×S) => f xs.1 xs.2) (x,sds.1) (dx,sds.2)
    -- ((y,dy),(s',ds'))
    pure ((r.1.1,r.2.1),(r.1.2, r.2.2))


  fwdFDerivM_pure f h :=
    by
      funext
      simp[pure, StateT.pure, fwdFDeriv]
      fun_trans
      simp [fwdFDeriv]

  fwdFDerivM_bind f g hf hg :=
    by
      funext x dx sds
      simp [DifferentiableM] at hf; simp [DifferentiableM] at hg
      simp[fwdFDeriv, bind, StateT.bind]
      fun_trans

  fwdFDerivM_pair f hf :=
    by
      funext x dx sds
      simp [DifferentiableM] at hf
      simp[bind, StateT.bind, pure, StateT.pure, Functor.map]
      fun_trans only
      simp


variable
  {S : Type} [NormedAddCommGroup S] [NormedSpace K S]
  {X : Type} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace K Z]

-- getThe ----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[simp, simp_core]
theorem _root_.getThe.arg.DifferentiableValM_rule
  : DifferentiableValM K (m:=StateT S m) (getThe S) :=
by
  simp[getThe, MonadStateOf.get, StateT.get,DifferentiableValM,DifferentiableM]
  fun_prop


@[simp, simp_core]
theorem _root_.getThe.arg.fwdFDerivValM_rule
  : fwdFDerivValM K (m:=StateT S m) (getThe S)
    =
    getThe (S×S) :=
by
  funext
  simp[getThe, MonadStateOf.get, StateT.get,fwdFDerivValM, fwdFDerivM, pure, StateT.pure]
  fun_trans

-- MonadStateOf.set ------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem _root_.MonadStateOf.set.arg_a0.DifferentiableM_rule
  (s : X → S) (ha0 : Differentiable K s)
  : DifferentiableM K (m:=StateT S m) (fun x => set (s x)) :=
by
  simp[set, StateT.set, DifferentiableValM, DifferentiableM]
  fun_prop


@[fun_trans]
theorem _root_.MonadStateOf.set.arg_a0.fwdFDerivM_rule
  (s : X → S) (ha0 : Differentiable K s)
  : fwdFDerivM K (m:=StateT S m) (fun x => set (s x))
    =
    (fun x dx => do
      let sds := fwdFDeriv K s x dx
      set sds
      pure ((),())) :=
by
  funext
  simp[set, StateT.set,fwdFDerivM, bind,Bind.bind, StateT.bind]
  fun_trans; congr


-- modifyThe ----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem _root_.modifyThe.arg_f.DifferentiableM_rule
  (f : X → S → S) (ha0 : Differentiable K (fun xs : X×S => f xs.1 xs.2))
  : DifferentiableM K (m:=StateT S m) (fun x => modifyThe S (f x)) :=
by
  simp[modifyThe, MonadStateOf.modifyGet, StateT.modifyGet, DifferentiableValM, DifferentiableM]
  fun_prop


@[fun_trans]
theorem _root_.modifyThe.arg_f.fwdFDerivM_rule
  (f : X → S → S) (ha0 : Differentiable K (fun xs : X×S => f xs.1 xs.2))
  : fwdFDerivM K (m:=StateT S m) (fun x => modifyThe S (f x))
    =
    (fun x dx => do
      modifyThe (S×S) (fun sds =>
        let sds := fwdFDeriv K (fun xs : X×S => f xs.1 xs.2) (x,sds.1) (dx,sds.2)
        sds)
      pure ((),())) :=
by
  funext
  simp[modifyThe, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,fwdFDerivM,bind,Bind.bind, StateT.bind]
  fun_trans; congr


-- modify ----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem _root_.modify.arg_f.DifferentiableM_rule
  (f : X → S → S) (ha0 : Differentiable K (fun xs : X×S => f xs.1 xs.2))
  : DifferentiableM K (m:=StateT S m) (fun x => modify (f x)) :=
by
  simp[modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, DifferentiableValM, DifferentiableM]
  fun_prop


@[fun_trans]
theorem _root_.modify.arg_f.fwdFDerivM_rule
  (f : X → S → S) (ha0 : Differentiable K (fun xs : X×S => f xs.1 xs.2))
  : fwdFDerivM K (m:=StateT S m) (fun x => modify (f x))
    =
    (fun x dx => do
      modify (fun sds =>
        let sds := fwdFDeriv K (fun xs : X×S => f xs.1 xs.2) (x,sds.1) (dx,sds.2)
        sds)
      pure ((),())) :=
by
  funext
  simp[modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,fwdFDerivM,bind,Bind.bind, StateT.bind]
  fun_trans; congr


end FwdFDerivMonad



section RevFDerivMonad

variable
  {K : Type _} [RCLike K]
  {m : Type → Type} {m' : outParam $ Type → Type} [Monad m] [Monad m']
  [DifferentiableMonad K m] [RevFDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']

@[simp]
theorem add_zero_left {α} [AddZeroClass α] :
  (HAdd.hAdd 0 : α → α) = fun x => x := by funext x; simp

open RevFDerivMonad in
noncomputable
instance (S : Type) [NormedAddCommGroup S] [AdjointSpace K S] [CompleteSpace S] :
    RevFDerivMonad K (StateT S m) (StateT S m') where
  revFDerivM f := fun x s => do
    let ysdf ← revFDerivM K (fun (xs : _×S) => f xs.1 xs.2) (x,s)
    pure ((ysdf.1.1, fun dx ds => ysdf.2 (dx,ds)), ysdf.1.2)

  revFDerivM_pure f h :=
    by
      funext
      simp[pure, StateT.pure, revFDeriv]
      fun_trans
      simp [revFDeriv]; rfl

  revFDerivM_bind f g hf hg :=
    by
      funext x s
      simp [DifferentiableM] at hf; simp [DifferentiableM] at hg
      simp[revFDeriv, bind, StateT.bind, StateT.pure, pure,Functor.map]
      fun_trans
      rfl

  revFDerivM_pair f hf :=
    by
      funext x s
      simp [DifferentiableM] at hf
      simp[bind, StateT.bind, pure, StateT.pure]
      fun_trans only
      simp
      congr; funext ysdf; congr; funext (dx,dy) ds; simp only [← bind_pure_comp]
      congr; funext (dx,ds); simp; rfl


variable
  {S : Type} [NormedAddCommGroup S] [AdjointSpace K S] [CompleteSpace S]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace K Z] [CompleteSpace Z]

-- getThe ----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[simp, simp_core]
theorem _root_.getThe.arg.revFDerivValM_rule
  : revFDerivValM K (m:=StateT S m) (getThe S)
    =
    (do
      pure ((← getThe S), fun ds => modifyThe S (fun ds' => ds + ds'))) :=
by
  funext
  simp[getThe, MonadStateOf.get, StateT.get,revFDerivValM, revFDerivM, pure, StateT.pure, bind, StateT.bind, set, StateT.set, modifyThe, modify, MonadStateOf.modifyGet, StateT.modifyGet]
  fun_trans; rfl

-- MonadState.get --------------------------------------------------------------
--------------------------------------------------------------------------------

@[simp, simp_core]
theorem _root_.MonadState.get.arg.revFDerivValM_rule
  : revFDerivValM K (m:=StateT S m) (get)
    =
    (do
      pure ((← get), fun ds => modify (fun ds' => ds + ds'))) :=
by
  funext
  simp[MonadState.get, getThe, MonadStateOf.get, StateT.get,revFDerivValM, revFDerivM, pure, StateT.pure, bind, StateT.bind, set, StateT.set, modifyThe, modify, MonadStateOf.modifyGet, StateT.modifyGet, modifyGet]
  fun_trans; rfl


-- MonadStateOf.set ------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem _root_.MonadStateOf.set.arg_a0.revFDerivM_rule
  (s : X → S) (ha0 : Differentiable K s)
  : revFDerivM K (m:=StateT S m) (fun x => set (s x))
    =
    (fun x => do
      let sds := revFDeriv K s x
      pure (← set sds.1,
            fun _ => do
              let dx := sds.2 (← get)
              set (0:S)
              pure dx)) :=
by
  funext
  simp[set, StateT.set, revFDerivM, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, get]
  fun_trans; congr; funext; simp[StateT.get, StateT.bind,StateT.set,StateT.pure]

-- -- modifyThe ----------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- @[fun_prop]
-- theorem _root_.modifyThe.arg_f.HasAdjDiffM_rule
--   (f : X → S → S) (ha0 : HasAdjDiff K (fun xs : X×S => f xs.1 xs.2))
--   : HasAdjDiffM K (m:=StateT S m) (fun x => modifyThe S (f x)) :=
-- by
--   simp[modifyThe, MonadStateOf.modifyGet, StateT.modifyGet, HasAdjDiffValM, HasAdjDiffM]
--   fun_prop


-- @[fun_trans]
-- theorem _root_.modifyThe.arg_f.revFDerivM_rule
--   (f : X → S → S) (ha0 : HasAdjDiff K (fun xs : X×S => f xs.1 xs.2))
--   : revFDerivM K (m:=StateT S m) (fun x => modifyThe S (f x))
--     =
--     (fun x => do
--       let sdf := revFDeriv K (fun xs : X×S => f xs.1 xs.2) (x, ← getThe S)
--       setThe S sdf.1
--       pure ((),
--             fun _ => do
--               let dxs := sdf.2 (← getThe S)
--               setThe S dxs.2
--               pure dxs.1)) :=
-- by
--   simp[modifyThe, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,revFDerivM, bind, StateT.bind, getThe, MonadStateOf.get, StateT.get, setThe, set, StateT.set]
--   fun_trans; congr


-- modify ----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem _root_.modify.arg_f.revFDerivM_rule
  (f : X → S → S) (ha0 : Differentiable K (fun xs : X×S => f xs.1 xs.2))
  : revFDerivM K (m:=StateT S m) (fun x => modify (f x))
    =
    (fun x => do
      let sdf := revFDeriv K (fun xs : X×S => f xs.1 xs.2) (x, ← get)
      set sdf.1
      pure ((),
            fun _ => do
              let dxs := sdf.2 (← get)
              set dxs.2
              pure dxs.1)) :=
by
  funext
  simp[modifyThe, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,revFDerivM, bind, StateT.bind, getThe, MonadStateOf.get, StateT.get, set, StateT.set, get, pure, StateT.pure, modify]
  fun_trans; congr; funext; simp[StateT.bind,StateT.pure,StateT.get,StateT.set]

end RevFDerivMonad
