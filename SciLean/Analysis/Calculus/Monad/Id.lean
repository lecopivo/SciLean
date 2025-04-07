import SciLean.Analysis.Calculus.Monad.FwdFDerivMonad
import SciLean.Analysis.Calculus.Monad.RevFDerivMonad
import SciLean.Analysis.Calculus.Monad.HasRevFDerivMonad

namespace SciLean

-- TODO: screw `Id` monad, define new `Id'` will wrap value in a structure
--       that way `Id'` can't abuse defeq and mess up the differentiation process

/-- Identity monad used for differentiating through imperative code.

When you write imperative code in `Id` monad and you want to differentiate it then please use `Id'`
instead. This is due to unfortunate fact that `Id X` is defeq `X` and this confuses autodiff
at some point. It leads to some unification issues that we were unable to solve. Using `Id'`
instead prevents defeq abuse and all these issues go away.
 -/
structure Id' (X : Type) where
  run : X

instance : Monad Id' where
  pure x := ⟨x⟩
  bind x f := f x.run

instance : LawfulMonad Id' where
  map_const := by aesop
  id_map := by aesop
  seqLeft_eq := by aesop
  seqRight_eq := by aesop
  pure_seq := by aesop
  bind_pure_comp := by aesop
  bind_map := by aesop
  pure_bind := by aesop
  bind_assoc := by aesop

@[simp, simp_core]
theorem Id'.run_pure {α} (a : α) : (pure a : Id' α).run = a := by rfl

instance : CoeHead (Id' X) X := ⟨fun x => x.run⟩
instance : Coe X (Id' X) := ⟨fun x => pure x⟩

variable
  {K : Type} [RCLike K]

instance : DifferentiableMonad K Id' where
  DifferentiableM f := Differentiable K (fun x => (f x).run)
  DifferentiableM_pure := by simp[pure]
  DifferentiableM_bind := by intros; simp[bind]; sorry_proof
  DifferentiableM_pair y := by intros; simp[bind,pure]; fun_prop

noncomputable
instance : FwdFDerivMonad K Id' Id' where
  fwdFDerivM f := fun x dx => pure (fwdFDeriv K (fun x => (f x).run) x dx)
  fwdFDerivM_pure f := by simp[pure]
  fwdFDerivM_bind := by simp[Id',Bind.bind]; sorry_proof
  fwdFDerivM_pair y := by intros; simp; sorry_proof

noncomputable
instance : RevFDerivMonad K Id' Id' where
  revFDerivM f := fun x =>
    let ydf := revFDeriv K (fun x => (f x).run) x
    pure (ydf.1, fun dy => pure (ydf.2 dy))
  revFDerivM_pure f := by simp[pure]
  revFDerivM_bind := by simp[Id',Bind.bind]; sorry_proof
  revFDerivM_pair y := by intros; simp; sorry_proof

instance : HasRevFDerivMonad K Id' Id' where
  HasRevFDerivM f f' :=
    HasRevFDeriv K
      (fun x => (f x).run)
      (fun x => let ydf := (f' x).run; (ydf.1, fun dy => (ydf.2 dy).run))
  HasRevFDerivM_pure f := by simp[pure]
  HasRevFDerivM_bind := by intros; simp[Id',Bind.bind]; sorry_proof
  HasRevFDerivM_pair y := by intros; simp; sorry_proof

end SciLean
open SciLean


section OnNormedSpace

variable
  {K : Type} [RCLike K]
  {X : Type} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace K Z]

@[fun_prop]
theorem Id'.run.arg_x.Differentiable_rule
    (a : X → Id' Y) (ha : DifferentiableM K a) :
    Differentiable K (fun x => Id'.run (a x)) := ha

@[fun_trans]
theorem Id'.run.arg_x.fwdFDeriv_rule (a : X → Id' Y) :
    fwdFDeriv K (fun x => Id'.run (a x))
    =
    fun x dx => (fwdFDerivM K a x dx).run := by rfl

end OnNormedSpace

section OnAdjointSpace

variable
  {K : Type} [RCLike K]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace K Z]

@[fun_trans]
theorem Id'.run.arg_x.revFDeriv_rule [CompleteSpace X] [CompleteSpace Y] (a : X → Id' Y) :
    revFDeriv K (fun x => Id'.run (a x))
    =
    fun x =>
      let xda := (revFDerivM K a x).run
      (xda.1,
       fun dy => (xda.2 dy).run) := by rfl


@[data_synth]
theorem Id'.HasRevFDerivM_const_rule (y : Id' Y) :
    HasRevFDerivM K (fun _ : X => y) (fun _ => pure (0, fun _ => pure 0)) := by
  sorry_proof

@[data_synth]
theorem Id'.HasRevFDerivUpdateM_const_rule (y : Id' Y) :
    HasRevFDerivUpdateM K (fun _ : X => y) (fun _ => pure (0, fun _ dx => pure dx)) := by
  sorry_proof

set_option linter.unusedVariables false in
@[data_synth]
theorem Id'.run.arg_x.HasRevFDeriv_rule
    (f : X → Id' Y) {f'} (hf : HasRevFDerivM K f f') :
    HasRevFDeriv K (fun x => (f x).run)
      (fun x => Id'.run do
        let ydf ← f' x
        pure (ydf.1, fun dy => Id'.run do
          let dx ← ydf.2 dy
          pure dx)) := sorry_proof

end OnAdjointSpace
