import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Tactic.DataSynth.Attr
import SciLean.Tactic.DataSynth.Elab
import SciLean.Tactic.LSimp.Elab

namespace SciLean

variable {R : Type} [RCLike R]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace R Z] [CompleteSpace Z]

variable (R)
@[data_synth out f' in f]
structure HasRevFDeriv (f : X → Y) (f' : X → Y×(Y→X))  where
  val : ∀ x, f' x = revFDeriv R f x
  prop : Differentiable R f
variable {R}


namespace HasRevFDeriv

@[data_synth]
theorem id_rule : HasRevFDeriv R (fun x : X => x) (fun x => (x, fun dx => dx)) := by
  constructor
  · fun_trans
  · fun_prop

set_option linter.unusedVariables false in
@[data_synth]
theorem const_rule (y : Y) :  HasRevFDeriv R (fun x : X => y) (fun x => (y, fun _ => 0)) := by
  constructor
  · fun_trans
  · fun_prop

theorem comp_rule (f : Y → Z) (g : X → Y) (f' g')
    (hf : HasRevFDeriv R f f') (hg : HasRevFDeriv R g g') :
    HasRevFDeriv R
      (fun x : X => f (g x))
      (fun x =>
        let ydy := g' x
        let y := ydy.1; let dg' := ydy.2
        let zdz := f' y
        let z := zdz.1; let df' := zdz.2
        (z, fun dz =>
              let dy := df' dz
              let dx := dg' dy
              dx)) := by

  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop

theorem let_rule (g : X → Y) (f : Y → X → Z) {f' g'}
    (hg : HasRevFDeriv R g g')
    (hf : HasRevFDeriv R (fun yx : Y×X => f yx.1 yx.2) f')  :
    HasRevFDeriv R
      (fun x : X => let y := g x; f y x)
      (fun x =>
        let ydy := g' x
        let y := ydy.1; let dg' := ydy.2
        let zdz := f' (y,x)
        let z := zdz.1; let df' := zdz.2
        (z, fun dz =>
          let dyx := df' dz
          let dx := dyx.2; let dy := dyx.1
          let dx' := dg' dy
          dx + dx')) := by

  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


end HasRevFDeriv

@[data_synth]
theorem Prod.mk.arg_a0a1.HasRevFDeriv_rule
  (f : X → Y) (g : X → Z) (f' g')
  (hf : HasRevFDeriv R f f') (hg : HasRevFDeriv R g g') :
  HasRevFDeriv R
    (fun x => (f x, g x))
    (fun x =>
      let ydy := f' x
      let y := ydy.1; let df' := ydy.2
      let zdz := g' x
      let z := zdz.1; let dg' := zdz.2
      ((y,z), fun dyz =>
        let dy := dyz.1; let dz := dyz.2
        let dx := df' dy
        let dx' := dg' dz
        dx + dx')) := by

  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop

@[data_synth]
theorem Prod.fst.arg_self.HasRevFDeriv_rule
  (f : X → Y×Z) (f')
  (hf : HasRevFDeriv R f f') :
  HasRevFDeriv R
    (fun x => (f x).1)
    (fun x =>
      let yzdyz := f' x
      let y := yzdyz.1.1; let df' := yzdyz.2
      (y, fun dy => df' (dy,0))) := by
  cases hf
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem Prod.snd.arg_self.HasRevFDeriv_rule
  (f : X → Y×Z) (f')
  (hf : HasRevFDeriv R f f') :
  HasRevFDeriv R
    (fun x => (f x).2)
    (fun x =>
      let yzdyz := f' x
      let z := yzdyz.1.2; let df' := yzdyz.2
      (z, fun dz => df' (0,dz))) := by
  cases hf
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasRevFDeriv_rule
    (f g : X → Y) (f' g')
    (hf : HasRevFDeriv R f f') (hg : HasRevFDeriv R g g') :
    HasRevFDeriv R (fun x => f x + g x)
      (fun x =>
        let ydy := f' x
        let y := ydy.1; let df' := ydy.2
        let zdz := g' x
        let z := zdz.1; let dg' := zdz.2
        (y + z, fun dx =>
                  let dy := df' dx
                  let dz := dg' dx
                  dy + dz)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop

@[data_synth]
theorem HSub.hSub.arg_a0a1.HasRevFDeriv_rule
    (f g : X → Y) (f' g')
    (hf : HasRevFDeriv R f f') (hg : HasRevFDeriv R g g') :
    HasRevFDeriv R (fun x => f x - g x)
      (fun x =>
        let ydy := f' x
        let y := ydy.1; let df' := ydy.2
        let zdz := g' x
        let z := zdz.1; let dg' := zdz.2
        (y - z, fun dx =>
                  let dy := df' dx
                  let dz := dg' dx
                  dy - dz)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


open ComplexConjugate
@[data_synth]
theorem HMul.hMul.arg_a0a1.HasRevFDeriv_rule
    (f g : X → R) (f' g')
    (hf : HasRevFDeriv R f f') (hg : HasRevFDeriv R g g') :
    HasRevFDeriv R (fun x => f x * g x)
      (fun x =>
        let ydy := f' x
        let y := ydy.1; let df' := ydy.2
        let zdz := g' x
        let z := zdz.1; let dg' := zdz.2
        (y * z, fun dx =>
           let dy := df' dx
           let dz := dg' dx
           (conj z) • dy + (conj y) • dz)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


omit [CompleteSpace X] [CompleteSpace Y] in
theorem HasRevFDeriv.revFDeriv {f : X → Y} {f'} (hf : HasRevFDeriv R f f') :
    revFDeriv R f = f' := by
  funext dx; cases hf
  simp_all [SciLean.revFDeriv]




open SciLean Lean Meta in
simproc [] dataSynthRevFDeriv (revFDeriv _ _ _) := fun e => do

  let .mkApp2 _ f x := e | return .continue
  let R := e.getArg! 0

  let h ← mkAppM ``HasRevFDeriv #[R,f]
  let (xs,_) ← forallMetaTelescope (← inferType h)
  let h := h.beta #[xs[0]!, x]

  let some goal ← Tactic.DataSynth.isDataSynthGoal? h
    | return .continue

  let (some r,_) ← Tactic.DataSynth.dataSynth goal |>.run {} |>.run {}
    | return .continue

  let e' := r.xs[0]!.beta #[x]

  return .visit { expr := e', proof? := ← mkAppM ``HasRevFDeriv.revFDeriv #[r.proof] }


set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.input true in

example : (revFDeriv R (fun x : R => x * x * x) 2)
          =
          fun dx => (2 * 2 * 2, 2 * 2 * dx + (2 * dx + dx * 2) * 2) := by
  conv =>
    lhs
    simp -zeta [dataSynthRevFDeriv]



set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.input true in
example : (revFDeriv R (fun x : R => let y := x * x; y * x) 2)
          =
          fun dx => (2 * 2 * 2, 2 * 2 * dx + (2 * dx + dx * 2) * 2) := by
  conv =>
    lhs
    simp -zeta [dataSynthRevFDeriv]



set_option trace.Meta.Tactic.data_synth true in
#check (HasRevFDeriv R (fun x : R => x) _ )
  rewrite_by
    data_synth


#check (HasRevFDeriv R (fun x : R => x*x) _ )
  rewrite_by
    data_synth


set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.normalize true in
#check (HasRevFDeriv R (fun x : R => let y := x; x) _ )
  rewrite_by
    data_synth


#check SciLean.HasRevFDeriv.let_rule


#check (HasRevFDeriv R (fun x : R => x*x*x*x) _ )
  rewrite_by
    data_synth


#check (HasRevFDeriv R (fun x : R => x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x) _ )
  rewrite_by
    data_synth




set_option trace.Meta.Tactic.data_synth true in
#check (HasRevFDeriv R (fun x : R => let y := x * x; y * x) _ )
  rewrite_by
    data_synth



set_option trace.Meta.Tactic.simp.rewrite true in
#check (revFDeriv R (fun x : R => let x₁ := x * x; let x₂ := x*x₁; let x₃ := x*x₁*x₂; x*x₁*x₂*x₃) 2)
  rewrite_by
    simp -zeta only [dataSynthRevFDeriv]


set_option profiler true in

#check (HasRevFDeriv R (fun x : R×R =>) _ 2)
  rewrite_by
    data_synth +lsimp -zeta
