import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Tactic.DataSynth.Attr
import SciLean.Tactic.DataSynth.Elab
import SciLean.Tactic.LSimp.Elab

set_option linter.unusedVariables false

namespace SciLean

variable {R : Type} [RCLike R]
  {X : Type} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace R Z]

variable (R)
@[data_synth out f' in f]
structure HasFwdFDeriv (f : X → Y) (f' : X → X → Y×Y) where
  val : ∀ x dx, f' x dx = (f x, fderiv R f x dx)
  prop : DifferentiableAt R f x
variable {R}


namespace HasFwdFDeriv

@[data_synth]
theorem id_rule (x : X) : HasFwdFDeriv R (fun x : X => x) (fun x dx => (x, dx)) := by
  constructor
  · fun_trans
  · fun_prop

set_option linter.unusedVariables false in
@[data_synth]
theorem const_rule (x : X) (y : Y) :  HasFwdFDeriv R (fun x : X => y) (fun x dx => (y, 0)) := by
  constructor
  · fun_trans
  · fun_prop

theorem comp_rule (f : Y → Z) (g : X → Y) (x : X) (f' g')
    (hf : HasFwdFDeriv R f f') (hg : HasFwdFDeriv R g g') :
    HasFwdFDeriv R
      (fun x : X => f (g x))
      (fun x dx =>
        let ydy := g' x dx
        f' ydy.1 ydy.2) := by

  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop

theorem let_rule (g : X → Y) (f : Y → X → Z) {x : X} {f' g'}
    (hg : HasFwdFDeriv R g g')
    (hf : HasFwdFDeriv R (fun yx : Y×X => f yx.1 yx.2) f')  :
    HasFwdFDeriv R
      (fun x : X => let y := g x; f y x)
      (fun x dx =>
        let ydy := g' x dx
        f' (ydy.1,x) (ydy.2,dx)) := by

  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all[Function.HasUncurry.uncurry]
  · fun_prop


end HasFwdFDeriv

@[data_synth]
theorem Prod.mk.arg_a0a1.HasFwdFDeriv_rule
  (f : X → Y) (g : X → Z) (f' g')
  (hf : HasFwdFDeriv R f f') (hg : HasFwdFDeriv R g g') :
  HasFwdFDeriv R
    (fun x => (f x, g x))
    (fun x dx =>
      let ydy := f' x dx
      let zdz := g' x dx
      ((ydy.1,zdz.1), (ydy.2, zdz.2))) := by

  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop

@[data_synth]
theorem Prod.fst.arg_self.HasFwdFDeriv_rule
  (f : X → Y×Z) (f')
  (hf : HasFwdFDeriv R f f') :
  HasFwdFDeriv R
    (fun x => (f x).1)
    (fun x dx =>
      let ydy := f' x dx
      (ydy.1.1, ydy.2.1)) := by
  cases hf
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop

@[data_synth]
theorem Prod.snd.arg_self.HasFwdFDeriv_rule
  (f : X → Y×Z) (f')
  (hf : HasFwdFDeriv R f f') :
  HasFwdFDeriv R
    (fun x => (f x).2)
    (fun x dx =>
      let ydy := f' x dx
      (ydy.1.2, ydy.2.2)) := by
  cases hf
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasFwdFDeriv_rule
    (f g : X → Y) (f' g')
    (hf : HasFwdFDeriv R f f') (hg : HasFwdFDeriv R g g') :
    HasFwdFDeriv R (fun x => f x + g x)
      (fun x dx =>
        let ydy := f' x dx
        let zdz := g' x dx
        (ydy.1 + zdz.1, ydy.2 + zdz.2)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem HSub.hSub.arg_a0a1.HasFwdFDeriv_rule
    (f g : X → Y) (f' g')
    (hf : HasFwdFDeriv R f f') (hg : HasFwdFDeriv R g g') :
    HasFwdFDeriv R (fun x => f x - g x)
      (fun x dx =>
        let ydy := f' x dx
        let zdz := g' x dx
        (ydy.1 - zdz.1, ydy.2 - zdz.2)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem HMul.hMul.arg_a0a1.HasFwdFDeriv_rule
    (f g : X → R) (f' g')
    (hf : HasFwdFDeriv R f f') (hg : HasFwdFDeriv R g g') :
    HasFwdFDeriv R (fun x => f x * g x)
      (fun x dx =>
        let ydy := f' x dx
        let zdz := g' x dx
        (ydy.1 * zdz.1, ydy.1 * zdz.2 + ydy.2 * zdz.1)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


theorem HasFwdFDeriv.fwdFDeriv {f : X → Y} {x} {f'} (hf : HasFwdFDeriv R f f') :
    fwdFDeriv R f x = f' x := by
  funext dx; cases hf
  unfold SciLean.fwdFDeriv
  simp_all
