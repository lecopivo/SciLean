import SciLean.Analysis.Calculus.Monad.FwdCDerivMonad
import SciLean.Analysis.Calculus.Monad.RevCDerivMonad

namespace SciLean


section FwdCDerivMonad

variable
  {K : Type _} [RCLike K]
  {m : Type → Type} {m' : outParam $ Type → Type} [Monad m] [Monad m'] [FwdCDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']


noncomputable
instance (S : Type _) [Vec K S] : FwdCDerivMonad K (StateT S m) (StateT (S×S) m') where
  fwdCDerivM f := fun x dx sds => do
    -- ((y,s'),(dy,ds'))
    let r ← fwdCDerivM K (fun (xs : _×S) => f xs.1 xs.2) (x,sds.1) (dx,sds.2)
    -- ((y,dy),(s',ds'))
    pure ((r.1.1,r.2.1),(r.1.2, r.2.2))

  CDifferentiableM f := CDifferentiableM K (fun (xs : _×S) => f xs.1 xs.2)

  fwdCDerivM_pure f h :=
    by
      funext
      simp[pure, StateT.pure, fwdCDeriv]
      fun_trans
      simp [fwdCDeriv]

  fwdCDerivM_bind f g hf hg :=
    by
      funext x dx sds
      simp at hf; simp at hg
      simp[fwdCDeriv, bind, StateT.bind, StateT.bind.match_1]
      fun_trans

  fwdCDerivM_pair f hf :=
    by
      funext x dx sds
      simp at hf
      simp[bind, StateT.bind, StateT.bind.match_1, pure, StateT.pure]
      fun_trans only
      simp

  CDifferentiableM_pure f hf :=
    by
      simp [Pure.pure,StateT.pure]
      fun_prop

  CDifferentiableM_bind f g hf hg :=
    by
      simp; simp at hf; simp at hg
      simp[bind, StateT.bind, StateT.bind.match_1]
      fun_prop

  CDifferentiableM_pair f hf :=
    by
      simp; simp at hf
      simp[bind, StateT.bind, StateT.bind.match_1, pure, StateT.pure]
      fun_prop



variable
  {S : Type _} [Vec K S]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]

-- getThe ----------------------------------------------------------------------
--------------------------------------------------------------------------------


@[simp, simp_core]
theorem _root_.getThe.arg.CDifferentiableValM_rule
  : CDifferentiableValM K (m:=StateT S m) (getThe S) :=
by
  simp[getThe, MonadStateOf.get, StateT.get,CDifferentiableValM,CDifferentiableM]
  fun_prop


@[simp, simp_core]
theorem _root_.getThe.arg.fwdCDerivValM_rule
  : fwdCDerivValM K (m:=StateT S m) (getThe S)
    =
    getThe (S×S) :=
by
  funext
  simp[getThe, MonadStateOf.get, StateT.get,fwdCDerivValM, fwdCDerivM, pure, StateT.pure]
  fun_trans

-- MonadState.get --------------------------------------------------------------
--------------------------------------------------------------------------------


@[simp,simp_core]
theorem _root_.MonadState.get.arg.CDifferentiableValM_rule
  : CDifferentiableValM K (m:=StateT S m) (get) :=
by
  simp[MonadState.get, getThe, MonadStateOf.get, StateT.get,CDifferentiableValM,CDifferentiableM]
  fun_prop

@[simp, simp_core]
theorem _root_.MonadState.get.arg.fwdCDerivValM_rule
  : fwdCDerivValM K (m:=StateT S m) (get)
    =
    get :=
by
  funext
  simp[MonadState.get, getThe, MonadStateOf.get, StateT.get,fwdCDerivValM, fwdCDerivM]
  fun_trans

-- -- setThe ----------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- @[fun_prop]
-- theorem _root_.setThe.arg_s.CDifferentiableM_rule
--   (s : X → S) (ha0 : CDifferentiable K s)
--   : CDifferentiableM K (m:=StateT S m) (fun x => setThe S (s x)) :=
-- by
--   simp[setThe, set, StateT.set, CDifferentiableValM, CDifferentiableM]
--   fun_prop


-- @[fun_trans]
-- theorem _root_.setThe.arg_s.fwdCDerivM_rule
--   (s : X → S) (hs : CDifferentiable K s)
--   : fwdCDerivM K (m:=StateT S m) (fun x => setThe S (s x))
--     =
--     (fun x dx => do
--       let sds := fwdCDeriv K s x dx
--       setThe _ sds
--       pure ((),())) :=
-- by
--   simp[setThe, set, StateT.set,fwdCDerivM,bind,Bind.bind, StateT.bind]
--   fun_trans; congr


-- MonadStateOf.set ------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem _root_.MonadStateOf.set.arg_a0.CDifferentiableM_rule
  (s : X → S) (ha0 : CDifferentiable K s)
  : CDifferentiableM K (m:=StateT S m) (fun x => set (s x)) :=
by
  simp[set, StateT.set, CDifferentiableValM, CDifferentiableM]
  fun_prop


@[fun_trans]
theorem _root_.MonadStateOf.set.arg_a0.fwdCDerivM_rule
  (s : X → S) (ha0 : CDifferentiable K s)
  : fwdCDerivM K (m:=StateT S m) (fun x => set (s x))
    =
    (fun x dx => do
      let sds := fwdCDeriv K s x dx
      set sds
      pure ((),())) :=
by
  funext
  simp[set, StateT.set,fwdCDerivM, bind,Bind.bind, StateT.bind]
  fun_trans; congr


-- modifyThe ----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem _root_.modifyThe.arg_f.CDifferentiableM_rule
  (f : X → S → S) (ha0 : CDifferentiable K (fun xs : X×S => f xs.1 xs.2))
  : CDifferentiableM K (m:=StateT S m) (fun x => modifyThe S (f x)) :=
by
  simp[modifyThe, MonadStateOf.modifyGet, StateT.modifyGet, CDifferentiableValM, CDifferentiableM]
  fun_prop


@[fun_trans]
theorem _root_.modifyThe.arg_f.fwdCDerivM_rule
  (f : X → S → S) (ha0 : CDifferentiable K (fun xs : X×S => f xs.1 xs.2))
  : fwdCDerivM K (m:=StateT S m) (fun x => modifyThe S (f x))
    =
    (fun x dx => do
      modifyThe (S×S) (fun sds =>
        let sds := fwdCDeriv K (fun xs : X×S => f xs.1 xs.2) (x,sds.1) (dx,sds.2)
        sds)
      pure ((),())) :=
by
  funext
  simp[modifyThe, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,fwdCDerivM,bind,Bind.bind, StateT.bind]
  fun_trans; congr


-- modify ----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem _root_.modify.arg_f.CDifferentiableM_rule
  (f : X → S → S) (ha0 : CDifferentiable K (fun xs : X×S => f xs.1 xs.2))
  : CDifferentiableM K (m:=StateT S m) (fun x => modify (f x)) :=
by
  simp[modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, CDifferentiableValM, CDifferentiableM]
  fun_prop


@[fun_trans]
theorem _root_.modify.arg_f.fwdCDerivM_rule
  (f : X → S → S) (ha0 : CDifferentiable K (fun xs : X×S => f xs.1 xs.2))
  : fwdCDerivM K (m:=StateT S m) (fun x => modify (f x))
    =
    (fun x dx => do
      modify (fun sds =>
        let sds := fwdCDeriv K (fun xs : X×S => f xs.1 xs.2) (x,sds.1) (dx,sds.2)
        sds)
      pure ((),())) :=
by
  funext
  simp[modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,fwdCDerivM,bind,Bind.bind, StateT.bind]
  fun_trans; congr


end FwdCDerivMonad


section RevCDerivMonad

variable
  {K : Type _} [RCLike K]
  {m : Type → Type} {m' : outParam $ Type → Type} [Monad m] [Monad m'] [RevCDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']

noncomputable
instance (S : Type _) [SemiInnerProductSpace K S] : RevCDerivMonad K (StateT S m) (StateT S m') where
  revCDerivM f := fun x s => do
    let ysdf ← revCDerivM K (fun (xs : _×S) => f xs.1 xs.2) (x,s)
    pure ((ysdf.1.1, fun dx ds => ysdf.2 (dx,ds)), ysdf.1.2)

  HasAdjDiffM f := HasAdjDiffM K (fun (xs : _×S) => f xs.1 xs.2)

  revCDerivM_pure f h :=
    by
      funext
      simp[pure, StateT.pure, revCDeriv]
      fun_trans
      simp [revCDeriv]; rfl

  revCDerivM_bind f g hf hg :=
    by
      funext x s
      simp at hf; simp at hg
      simp[revCDeriv, bind, StateT.bind, StateT.bind.match_1, StateT.pure, pure]
      fun_trans
      rfl

  revCDerivM_pair f hf :=
    by
      funext x s
      simp at hf
      simp[bind, StateT.bind, StateT.bind.match_1, pure, StateT.pure]
      fun_trans only
      simp
      congr; funext ysdf; congr; funext dx ds; congr; funext (dx,ds); simp; rfl

  HasAdjDiffM_pure f hf :=
    by
      simp [pure,StateT.pure]
      fun_prop

  HasAdjDiffM_bind f g hf hg :=
    by
      simp; simp at hf; simp at hg
      simp[bind, StateT.bind, StateT.bind.match_1]
      fun_prop

  HasAdjDiffM_pair f hf :=
    by
      simp; simp at hf
      simp[bind, StateT.bind, StateT.bind.match_1, pure, StateT.pure]
      fun_prop

variable
  {S : Type _} [SemiInnerProductSpace K S]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]

-- getThe ----------------------------------------------------------------------
--------------------------------------------------------------------------------


@[simp, simp_core]
theorem _root_.getThe.arg.HasAdjDiffValM_rule
  : HasAdjDiffValM K (m:=StateT S m) (getThe S) :=
by
  simp[getThe, MonadStateOf.get, StateT.get,HasAdjDiffValM,HasAdjDiffM]
  fun_prop


@[simp, simp_core]
theorem _root_.getThe.arg.revCDerivValM_rule
  : revCDerivValM K (m:=StateT S m) (getThe S)
    =
    (do
      pure ((← getThe S), fun ds => modifyThe S (fun ds' => ds + ds'))) :=
by
  funext
  simp[getThe, MonadStateOf.get, StateT.get,revCDerivValM, revCDerivM, pure, StateT.pure, bind, StateT.bind, set, StateT.set, modifyThe, modify, MonadStateOf.modifyGet, StateT.modifyGet]
  fun_trans; rfl

-- MonadState.get --------------------------------------------------------------
--------------------------------------------------------------------------------


@[simp, simp_core]
theorem _root_.MonadState.get.arg.HasAdjDiffValM_rule
  : HasAdjDiffValM K (m:=StateT S m) (get) :=
by
  simp[MonadState.get, getThe, MonadStateOf.get, StateT.get,HasAdjDiffValM,HasAdjDiffM]
  fun_prop


@[simp, simp_core]
theorem _root_.MonadState.get.arg.revCDerivValM_rule
  : revCDerivValM K (m:=StateT S m) (get)
    =
    (do
      pure ((← get), fun ds => modify (fun ds' => ds + ds'))) :=
by
  funext
  simp[MonadState.get, getThe, MonadStateOf.get, StateT.get,revCDerivValM, revCDerivM, pure, StateT.pure, bind, StateT.bind, set, StateT.set, modifyThe, modify, MonadStateOf.modifyGet, StateT.modifyGet, modifyGet]
  fun_trans; rfl


-- -- setThe ----------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- @[fun_prop]
-- theorem _root_.setThe.arg_s.HasAdjDiffM_rule
--   (s : X → S) (ha0 : HasAdjDiff K s)
--   : HasAdjDiffM K (m:=StateT S m) (fun x => setThe S (s x)) :=
-- by
--   simp[setThe, set, StateT.set, HasAdjDiffValM, HasAdjDiffM]
--   fun_prop


-- @[fun_trans]
-- theorem _root_.setThe.arg_s.revCDerivM_rule
--   (s : X → S) (hs : HasAdjDiff K s)
--   : revCDerivM K (m:=StateT S m) (fun x => setThe S (s x))
--     =
--     (fun x => do
--       let sds := revCDeriv K s x
--       pure (← setThe S sds.1,
--             fun _ => do
--               let dx := sds.2 (← getThe S)
--               setThe S 0
--               pure dx)) :=
-- by
--   simp[setThe, set, StateT.set, revCDerivM, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure]
--   fun_trans


-- MonadStateOf.set ------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem _root_.MonadStateOf.set.arg_a0.HasAdjDiffM_rule
  (s : X → S) (ha0 : HasAdjDiff K s)
  : HasAdjDiffM K (m:=StateT S m) (fun x => set (s x)) :=
by
  simp[set, StateT.set, HasAdjDiffValM, HasAdjDiffM]
  fun_prop


@[fun_trans]
theorem _root_.MonadStateOf.set.arg_a0.revCDerivM_rule
  (s : X → S) (ha0 : HasAdjDiff K s)
  : revCDerivM K (m:=StateT S m) (fun x => set (s x))
    =
    (fun x => do
      let sds := revCDeriv K s x
      pure (← set sds.1,
            fun _ => do
              let dx := sds.2 (← get)
              set (0:S)
              pure dx)) :=
by
  funext
  simp[set, StateT.set, revCDerivM, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, get]
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
-- theorem _root_.modifyThe.arg_f.revCDerivM_rule
--   (f : X → S → S) (ha0 : HasAdjDiff K (fun xs : X×S => f xs.1 xs.2))
--   : revCDerivM K (m:=StateT S m) (fun x => modifyThe S (f x))
--     =
--     (fun x => do
--       let sdf := revCDeriv K (fun xs : X×S => f xs.1 xs.2) (x, ← getThe S)
--       setThe S sdf.1
--       pure ((),
--             fun _ => do
--               let dxs := sdf.2 (← getThe S)
--               setThe S dxs.2
--               pure dxs.1)) :=
-- by
--   simp[modifyThe, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,revCDerivM, bind, StateT.bind, getThe, MonadStateOf.get, StateT.get, setThe, set, StateT.set]
--   fun_trans; congr


-- modify ----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem _root_.modify.arg_f.HasAdjDiffM_rule
  (f : X → S → S) (ha0 : HasAdjDiff K (fun xs : X×S => f xs.1 xs.2))
  : HasAdjDiffM K (m:=StateT S m) (fun x => modify (f x)) :=
by
  simp[modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, HasAdjDiffValM, HasAdjDiffM]
  fun_prop


@[fun_trans]
theorem _root_.modify.arg_f.revCDerivM_rule
  (f : X → S → S) (ha0 : HasAdjDiff K (fun xs : X×S => f xs.1 xs.2))
  : revCDerivM K (m:=StateT S m) (fun x => modify (f x))
    =
    (fun x => do
      let sdf := revCDeriv K (fun xs : X×S => f xs.1 xs.2) (x, ← get)
      set sdf.1
      pure ((),
            fun _ => do
              let dxs := sdf.2 (← get)
              set dxs.2
              pure dxs.1)) :=
by
  funext
  simp[modifyThe, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,revCDerivM, bind, StateT.bind, getThe, MonadStateOf.get, StateT.get, set, StateT.set, get, pure, StateT.pure, modify]
  fun_trans; congr; funext; simp[StateT.bind,StateT.pure,StateT.get,StateT.set]

end RevCDerivMonad
