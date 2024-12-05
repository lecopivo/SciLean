import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Tactic.DataSynth.Attr
import SciLean.Tactic.DataSynth.Elab
import SciLean.Tactic.LSimp.Elab

namespace SciLean

variable {R : Type} [RCLike R]
  {X : Type} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace R Z]

variable (R)
@[data_synth out f' in f]
structure HasFwdFDerivAt (f : X → Y) (f' : X → X → Y×Y) (x : X) where
  val : ∀ dx, f' x dx = (f x, fderiv R f x dx)
  prop : DifferentiableAt R f x
variable {R}


namespace HasFwdFDerivAt

@[data_synth]
theorem id_rule (x : X) : HasFwdFDerivAt R (fun x : X => x) (fun x dx => (x, dx)) x := by
  constructor
  · fun_trans
  · fun_prop

set_option linter.unusedVariables false in
@[data_synth]
theorem const_rule (x : X) (y : Y) :  HasFwdFDerivAt R (fun x : X => y) (fun x dx => (y, 0)) x := by
  constructor
  · fun_trans
  · fun_prop

theorem comp_rule (f : Y → Z) (g : X → Y) (x : X) (f' g')
    (hf : HasFwdFDerivAt R f f' (g x)) (hg : HasFwdFDerivAt R g g' x) :
    HasFwdFDerivAt R
      (fun x : X => f (g x))
      (fun x dx =>
        let ydy := g' x dx
        f' ydy.1 ydy.2) x := by

  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop

theorem let_rule (g : X → Y) (f : Y → X → Z) {x : X} {f' g'}
    (hg : HasFwdFDerivAt R g g' x)
    (hf : HasFwdFDerivAt R (fun yx : Y×X => f yx.1 yx.2) f' (g x, x))  :
    HasFwdFDerivAt R
      (fun x : X => let y := g x; f y x)
      (fun x dx =>
        let ydy := g' x dx
        f' (ydy.1,x) (ydy.2,dx)) x := by

  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all[Function.HasUncurry.uncurry]
  · fun_prop


end HasFwdFDerivAt

@[data_synth]
theorem Prod.mk.arg_a0a1.HasFwdFDerivAt_rule
  (f : X → Y) (g : X → Z) (x) (f' g')
  (hf : HasFwdFDerivAt R f f' x) (hg : HasFwdFDerivAt R g g' x) :
  HasFwdFDerivAt R
    (fun x => (f x, g x))
    (fun x dx =>
      let ydy := f' x dx
      let zdz := g' x dx
      ((ydy.1,zdz.1), (ydy.2, zdz.2))) x := by

  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop

@[data_synth]
theorem Prod.fst.arg_self.HasFwdFDerivAt_rule
  (f : X → Y×Z) (x) (f')
  (hf : HasFwdFDerivAt R f f' x) :
  HasFwdFDerivAt R
    (fun x => (f x).1)
    (fun x dx =>
      let ydy := f' x dx
      (ydy.1.1, ydy.2.1)) x := by
  cases hf
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop

@[data_synth]
theorem Prod.snd.arg_self.HasFwdFDerivAt_rule
  (f : X → Y×Z) (x) (f')
  (hf : HasFwdFDerivAt R f f' x) :
  HasFwdFDerivAt R
    (fun x => (f x).2)
    (fun x dx =>
      let ydy := f' x dx
      (ydy.1.2, ydy.2.2)) x := by
  cases hf
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasFwdFDerivAt_rule
    (f g : X → Y) (x) (f' g')
    (hf : HasFwdFDerivAt R f f' x) (hg : HasFwdFDerivAt R g g' x) :
    HasFwdFDerivAt R (fun x => f x + g x)
      (fun x dx =>
        let ydy := f' x dx
        let zdz := g' x dx
        (ydy.1 + zdz.1, ydy.2 + zdz.2)) x := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem HSub.hSub.arg_a0a1.HasFwdFDerivAt_rule
    (f g : X → Y) (x) (f' g')
    (hf : HasFwdFDerivAt R f f' x) (hg : HasFwdFDerivAt R g g' x) :
    HasFwdFDerivAt R (fun x => f x - g x)
      (fun x dx =>
        let ydy := f' x dx
        let zdz := g' x dx
        (ydy.1 - zdz.1, ydy.2 - zdz.2)) x := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem HMul.hMul.arg_a0a1.HasFwdFDerivAt_rule
    (f g : X → R) (x) (f' g')
    (hf : HasFwdFDerivAt R f f' x) (hg : HasFwdFDerivAt R g g' x) :
    HasFwdFDerivAt R (fun x => f x * g x)
      (fun x dx =>
        let ydy := f' x dx
        let zdz := g' x dx
        (ydy.1 * zdz.1, ydy.1 * zdz.2 + ydy.2 * zdz.1)) x := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


theorem HasFwdFDerivAt.fwdFDeriv {f : X → Y} {x} {f'} (hf : HasFwdFDerivAt R f f' x) :
    fwdFDeriv R f x = f' x := by
  funext dx; cases hf
  unfold SciLean.fwdFDeriv
  simp_all

#exit

open SciLean Lean Meta in
simproc [] dataSynthFwdFDeriv (fwdFDeriv _ _ _) := fun e => do

  let .mkApp2 _ f x := e | return .continue
  let R := e.getArg! 0

  let h ← mkAppM ``HasFwdFDerivAt #[R,f]
  let (xs,_) ← forallMetaTelescope (← inferType h)
  let h := h.beta #[xs[0]!, x]

  let some goal ← Tactic.DataSynth.isDataSynthGoal? h
    | return .continue

  let (some r,_) ← Tactic.DataSynth.dataSynth goal |>.run {} |>.run {}
    | return .continue

  let e' := r.xs[0]!.beta #[x]

  return .visit { expr := e', proof? := ← mkAppM ``HasFwdFDerivAt.fwdFDeriv #[r.proof] }


set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.input true in

example : (fwdFDeriv R (fun x : R => x * x * x) 2)
          =
          fun dx => (2 * 2 * 2, 2 * 2 * dx + (2 * dx + dx * 2) * 2) := by
  conv =>
    lhs
    simp -zeta [dataSynthFwdFDeriv]



set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.input true in
example : (fwdFDeriv R (fun x : R => let y := x * x; y * x) 2)
          =
          fun dx => (2 * 2 * 2, 2 * 2 * dx + (2 * dx + dx * 2) * 2) := by
  conv =>
    lhs
    simp -zeta [dataSynthFwdFDeriv]


#check (HasFwdFDerivAt R (fun x : R => let y := x * x; y * x) _ 2)
  rewrite_by
    data_synth



set_option trace.Meta.Tactic.simp.rewrite true in
#check (fwdFDeriv R (fun x : R => let x₁ := x * x; let x₂ := x*x₁; let x₃ := x*x₁*x₂; x*x₁*x₂*x₃) 2)
  rewrite_by
    simp -zeta only [dataSynthFwdFDeriv]


set_option profiler true in

#check (HasFwdFDerivAt R (fun x : R×R =>) _ 2)
  rewrite_by
    data_synth +lsimp -zeta
