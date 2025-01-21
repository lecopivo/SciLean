import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Tactic.DataSynth.Attr
import SciLean.Tactic.DataSynth.Elab
import SciLean.Tactic.Autodiff
import SciLean.Meta.Notation.Let'
import SciLean.Util.Profile

set_option linter.unusedVariables false

namespace SciLean

variable {R : Type*} [RCLike R]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]
  {Z : Type*} [NormedAddCommGroup Z] [AdjointSpace R Z] [CompleteSpace Z]
  {X₁ : Type*} [NormedAddCommGroup X₁] [AdjointSpace R X₁] [CompleteSpace X₁]
  {X₂ : Type*} [NormedAddCommGroup X₂] [AdjointSpace R X₂] [CompleteSpace X₂]


variable (R)
@[data_synth out f' in f]
structure HasRevFDeriv (f : X → Y) (f' : X → Y×(Y→X))  where
  val : ∀ x, f' x = revFDeriv R f x
  prop : Differentiable R f
variable {R}

omit [CompleteSpace X] [CompleteSpace Y] in
theorem HasRevFDeriv.revFDeriv {f : X → Y} {f'} (hf : HasRevFDeriv R f f') :
    revFDeriv R f = f' := by
  funext dx; cases hf
  simp_all [SciLean.revFDeriv]


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


omit [CompleteSpace X] [CompleteSpace Y] [CompleteSpace X₁] [AdjointSpace R X₂] [CompleteSpace X₂] in
theorem proj_rule (f : X → Y) {g'}
    (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X)
    (hg : HasRevFDeriv R g g') :
    HasRevFDeriv R f (fun x =>
      let x₁ := p₁ x
      let' (y,dg) := g' x₁;
      (y, fun dy =>
        let dz := dg dy
        q dz 0)) := by sorry_proof


theorem comp_rule (g : X → Y) (f : Y → Z) (f' g')
    (hg : HasRevFDeriv R g g') (hf : HasRevFDeriv R f f') :
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
theorem Prod.fst.arg_self.HasRevFDeriv_rule' :
  HasRevFDeriv R
    (fun x : X×Y => x.1)
    (fun x =>
      (x.1, fun dz => (dz,0))) := by
  constructor
  · intro dx; fun_trans only
  · fun_prop


@[data_synth]
theorem Prod.snd.arg_self.HasRevFDeriv_rule' :
  HasRevFDeriv R
    (fun x : X×Y => x.2)
    (fun x =>
      (x.2, fun dz => (0,dz))) := by
  constructor
  · intro dx; fun_trans only
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


@[data_synth]
theorem HPow.hPow.arg_a0a1.HasRevFDeriv_rule_nat
    (f : X → R) (f') (n : ℕ)
    (hf : HasRevFDeriv R f f') :
    HasRevFDeriv R (fun x => f x ^ n)
      (fun x =>
        let' (y,df) := f' x
        (y ^ n, fun dx =>
           let dy := df dx
           (n * (conj y) ^ (n-1)) • dy)) := by
  cases hf;
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop
