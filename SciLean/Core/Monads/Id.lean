import SciLean.Core.Monads.FwdDerivMonad
import SciLean.Core.Monads.RevDerivMonad

namespace SciLean

variable
  {K : Type _} [RCLike K]

instance [Vec K X] : Vec K (Id X) := by unfold Id; infer_instance
instance [SemiInnerProductSpace K X] : SemiInnerProductSpace K (Id X) := by unfold Id; infer_instance
-- instance [FinVec ι K X] : SemiInnerProductSpace K (Id X) := by unfold Id; infer_instance

noncomputable
instance : FwdDerivMonad K Id Id where
  fwdDerivM f := fwdDeriv K f
  CDifferentiableM f := CDifferentiable K f
  fwdDerivM_pure f := by simp[pure]
  fwdDerivM_bind := by simp[Id]; intros; fun_trans
  fwdDerivM_pair y := by intros; simp; fun_trans
  CDifferentiableM_pure := by simp[pure]
  CDifferentiableM_bind := by simp[bind]; fprop
  CDifferentiableM_pair y :=
    by
      intros; simp[bind]; -- fprop something goes wrong where :(
      have h : CDifferentiable K (fun x : _ => (x, y x)) := by fprop
      apply h


noncomputable
instance : RevDerivMonad K Id Id where
  revDerivM f := revDeriv K f
  HasAdjDiffM f := HasAdjDiff K f
  revDerivM_pure f := by intros; funext; simp[pure,revDeriv]
  revDerivM_bind := by intros; simp; fun_trans; rfl
  revDerivM_pair y := by intros; simp; fun_trans; simp[revDeriv]
  HasAdjDiffM_pure := by simp[pure]
  HasAdjDiffM_bind := by simp[bind]; fprop
  HasAdjDiffM_pair y :=
    by
      intros; simp[bind]; -- fprop something goes wrong where :(
      have h : HasAdjDiff K (fun x : _ => (x, y x)) := by fprop
      apply h


end SciLean
open SciLean


section OnVec

variable
  {K : Type _} [RCLike K]
  {X : Type} [Vec K X]
  {Y : Type} [Vec K Y]
  {Z : Type} [Vec K Z]
  {E : ι → Type _} [∀ i, Vec K (E i)]

@[fprop]
theorem Id.run.arg_x.CDifferentiable_rule
  (a : X → Id Y) (ha : CDifferentiableM K a)
  : CDifferentiable K (fun x => Id.run (a x)) := ha

@[fun_trans]
theorem Id.run.arg_x.fwdDeriv_rule (a : X → Id Y)
  : fwdDeriv K (fun x => Id.run (a x))
    =
    fun x dx => (fwdDerivM K a x dx) := by rfl

end OnVec

section OnSemiInnerProductSpace

variable
  {K : Type _} [RCLike K]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]


@[fprop]
theorem Id.run.arg_x.HasAdjDiff_rule
  (a : X → Id Y) (ha : HasAdjDiffM K a)
  : HasAdjDiff K (fun x => Id.run (a x)) := ha

@[fun_trans]
theorem Id.run.arg_x.revDeriv_rule (a : X → Id Y)
  : revDeriv K (fun x => Id.run (a x))
    =
    fun x => (revDerivM K a x) := by rfl


-- some normalizations for Id monad because it is pain in the ass to work with
-- as one can often abuse defEq

-- @[fun_trans_simp]
-- theorem revDerivM_eq_revDeriv_on_Id (f : X → Y)
--   : revDerivM (m:=Id) K f = fun x => pure (revDeriv K f x) := by rfl

-- @[fun_trans_simp]
-- theorem revDerivM_eq_revDeriv_on_Id' (f : X → Id Y)
--   : revDerivM K f = revDeriv K f := by set_option pp.all true in rfl

@[fprop]
theorem Pure.pure.arg_a0.HasAdjDiff_rule
  (a0 : X → Y)
  (ha0 : HasAdjDiff K a0)
  : HasAdjDiff K (fun x => Pure.pure (f:=Id) (a0 x)) :=
by
  simp[Pure.pure]; fprop

@[fprop]
theorem Bind.bind.arg_a0a1.HasAdjDiff_rule_on_Id
  (a0 : X → Y) (a1 : X → Y → Z)
  (ha0 : HasAdjDiff K a0) (ha1 : HasAdjDiff K (fun (x,y) => a1 x y))
  : HasAdjDiff K (fun x => Bind.bind (m:=Id) (a0 x) (a1 x)) := by simp[Bind.bind]; fprop


@[fun_trans]
theorem Bind.bind.arg_a0a1.revDerivM_rule_on_Id
  (a0 : X → Y) (a1 : X → Y → Z)
  (ha0 : HasAdjDiff K a0) (ha1 : HasAdjDiff K (fun (x,y) => a1 x y))
  : (revDerivM (m:=Id) K (fun x => Bind.bind (a0 x) (a1 x)))
    =
    fun x =>
      let ydg' := revDeriv K a0 x
      let zdf' := revDeriv K (fun (x,y) => a1 x y) (x,ydg'.1)
      (zdf'.1,
       fun dz' =>
         let dxy' := zdf'.2 dz'
         let dx' := ydg'.2 dxy'.2
         dxy'.1 + dx') :=
by
  simp[revDerivM]; fun_trans; simp[revDeriv]

-- @[fun_trans]
-- This theorem causes some downstream issue in simp when applying congruence lemmas
-- The issue seems that there is some defEq abuse that stop working
theorem Bind.bind.arg_a0a1.revDeriv_rule_on_Id
  (a0 : X → Y) (a1 : X → Y → Z)
  (ha0 : HasAdjDiff K a0) (ha1 : HasAdjDiff K (fun (x,y) => a1 x y))
  : (revDeriv K (fun x => Bind.bind (m:=Id) (a0 x) (a1 x)))
    =
    fun x =>
      let ydg' := revDeriv K a0 x
      let zdf' := revDeriv K (fun (x,y) => a1 x y) (x,ydg'.1)
      (zdf'.1,
       fun dz' =>
         let dxy' := zdf'.2 dz'
         let dx' := ydg'.2 dxy'.2
         dxy'.1 + dx') :=
by
  simp (config := {zeta:=false}) [Bind.bind]; fun_trans; rfl



end OnSemiInnerProductSpace
