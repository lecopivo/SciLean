import SciLean.Tactic.DataSynth.HasRevFDeriv
import SciLean.Analysis.SpecialFunctions.Inner
import SciLean.Analysis.SpecialFunctions.Norm2

set_option linter.unusedVariables false

namespace SciLean

variable {R : Type} [RCLike R]
  {W : Type} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace R Z] [CompleteSpace Z]
  {X₁ : Type} [NormedAddCommGroup X₁] [AdjointSpace R X₁] [CompleteSpace X₁]
  {X₂ : Type} [NormedAddCommGroup X₂] [AdjointSpace R X₂] [CompleteSpace X₂]


variable (R)
@[data_synth out f' in f]
structure HasRevFDerivUpdate (f : X → Y) (f' : X → Y×(Y→X→X))  where
  val : ∀ x, f' x
             =
             let' (y,df) := revFDeriv R f x;
             (y, fun dy dx => dx + df dy)
  prop : Differentiable R f
variable {R}


namespace HasRevFDerivUpdate

@[data_synth]
theorem id_rule : HasRevFDerivUpdate R (fun x : X => x) (fun x => (x, fun dx dx₀ => dx₀ + dx)) := by
  constructor
  · fun_trans
  · fun_prop


theorem const_rule (y : Y) :  HasRevFDerivUpdate R (fun x : X => y) (fun x => (y, fun _ dx => dx)) := by
  constructor
  · fun_trans
  · fun_prop


theorem comp_rule (f : Y → Z) (g : X → Y) (f' g')
    (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
    HasRevFDerivUpdate R
      (fun x : X => f (g x))
      (fun x =>
        let' (y,dg) := g' x
        let' (z,df) := f' y
        (z, fun dz dx =>
              let dy := df dz 0
              dg dy dx)) := by

  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


theorem let_rule (g : X → Y) (f : Y → X → Z) {f' g'}
    (hg : HasRevFDerivUpdate R g g')
    (hf : HasRevFDerivUpdate R (fun yx : Y×X => f yx.1 yx.2) f')  :
    HasRevFDerivUpdate R
      (fun x : X => let y := g x; f y x)
      (fun x =>
        let' (y,dg) := g' x
        let' (z,df) := f' (y,x)
        (z, fun dz dx =>
          let' (dy,dx) := df dz (0,dx);
          dg dy dx)) := by

  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all; ac_rfl
  · fun_prop


omit [CompleteSpace X] [CompleteSpace Y] [CompleteSpace X₁] [AdjointSpace R X₂] [CompleteSpace X₂] [NormedAddCommGroup X₂] in
theorem proj_rule (f : X → Y) {g'}
    (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X)
    (hg : HasRevFDerivUpdate R g g') :
    HasRevFDerivUpdate R f (fun x =>
      let x₁ := p₁ x
      let' (y,dg) := g' x₁;
      (y, fun dy dx =>
        let dx₁ := p₁ dx
        let dx₂ := p₂ dx
        let dx₁ := dg dy dx₁
        q dx₁ dx₂)) := by sorry_proof


end HasRevFDerivUpdate

@[data_synth]
theorem Prod.mk.arg_a0a1.HasRevFDerivUpdate_rule
  (f : X → Y) (g : X → Z) (f' g')
  (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
  HasRevFDerivUpdate R
    (fun x => (f x, g x))
    (fun x =>
      let' (y,df) := f' x
      let' (z,dg) := g' x
      ((y,z), fun dyz dx =>
        let' (dy,dz) := dyz
        let dx := df dy dx
        dg dz dx)) := by

  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all; ac_rfl
  · fun_prop

@[data_synth]
theorem Prod.fst.arg_self.HasRevFDerivUpdate_rule
  (f : X → Y×Z) (f')
  (hf : HasRevFDerivUpdate R f f') :
  HasRevFDerivUpdate R
    (fun x => (f x).1)
    (fun x =>
      let' ((y,z),df) := f' x
      (y, fun dy dx => df (dy,0) dx)) := by
  cases hf
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop

@[data_synth]
theorem Prod.snd.arg_self.HasRevFDerivUpdate_rule
  (f : X → Y×Z) (f')
  (hf : HasRevFDerivUpdate R f f') :
  HasRevFDerivUpdate R
    (fun x => (f x).2)
    (fun x =>
      let' ((y,z),df) := f' x
      (z, fun dz dx => df (0,dz) dx)) := by
  cases hf
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasRevFDerivUpdate_rule
    (f g : X → Y) (f' g')
    (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
    HasRevFDerivUpdate R (fun x => f x + g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y + z, fun dy dx =>
                  let dx := df dy dx
                  dg dy dx)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all; ac_rfl
  · fun_prop


@[data_synth]
theorem HSub.hSub.arg_a0a1.HasRevFDerivUpdate_rule
    (f g : X → Y) (f' g')
    (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
    HasRevFDerivUpdate R (fun x => f x - g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y - z, fun dy dx =>
                  let dx := df dy dx
                  dg (-dy) dx)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only;
    simp_all[revFDeriv,neg_pull]
    funext dy dx
    abel
  · fun_prop


open ComplexConjugate
@[data_synth]
theorem HMul.hMul.arg_a0a1.HasRevFDerivUpdate_rule
    (f g : X → R) (f' g')
    (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
    HasRevFDerivUpdate R (fun x => f x * g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y * z, fun dy dx =>
           let dy₁ := (conj z) • dy
           let dy₂ := (conj y) • dy
           let dx := df dy₁ dx
           let dx := dg dy₂ dx
           dx)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
    funext dy dx
    simp[revFDeriv,smul_push]
    ac_rfl
  · fun_prop


@[data_synth]
theorem HSMul.hSMul.arg_a0a1.HasRevFDerivUpdate_rule
    (f : X → R) (g : X → Y) (f' g')
    (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
    HasRevFDerivUpdate R (fun x => f x • g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y • z, fun dy dx =>
           let dy₁ := ⟪z, dy⟫[R]
           let dy₂ := (conj y) • dy
           let dx := df dy₁ dx
           let dx := dg dy₂ dx
           dx)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
    funext dy dx
    simp[revFDeriv,smul_push]
    ac_rfl
  · fun_prop


#check Nat


@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.HasRevFDerivUpdate_rule
    (f g : X → R) (f' g')
    (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') (hx : ∀ x, g x ≠ 0) :
    HasRevFDerivUpdate R
     (fun x => f x / g x)
     (fun x =>
       let' (y,df) := f' x
       let' (z,dg) := g' x
       (y / z,
         fun dr dx =>
           let s := ((conj z)^2)⁻¹
           let dx := df (s*(conj z)*dr) dx
           let dx := dg (-s*(conj y)*dr) dx
           dx)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans (disch:=apply hx) only; simp_all
    funext dy dx
    simp[revFDeriv,smul_push,neg_pull,sub_eq_add_neg]
    ac_rfl
  · sorry_proof
    --fun_prop (disch:=apply hx) -- missing theorem about division



@[data_synth]
theorem HInv.hInv.arg_a0.HasRevFDerivUpdate_rule
  (f : X → R) (f')
  (hf : HasRevFDerivUpdate R f f') (hx : ∀ x, f x ≠ 0) :
  HasRevFDerivUpdate R (fun x => (f x)⁻¹)
    (fun x =>
      let' (y,df) := f' x
      (y⁻¹, fun dy dx =>
        let dx := df (-((conj y)^2)⁻¹*dy) dx
        dx)) := by
  cases hf
  constructor
  · intro dx; fun_trans (disch:=apply hx) only; simp_all
    funext dy dx
    simp[revFDeriv,neg_pull,smul_push]
  · sorry_proof


@[data_synth]
theorem HPow.hPow.arg_a0.HasRevFDerivUpdate_rule
  (f : X → R) (n : ℕ) (f')
  (hf : HasRevFDerivUpdate R f f') :
  HasRevFDerivUpdate R (fun x => f x ^ n)
    (fun x =>
      let' (y,df) := f' x
      (y ^ n, fun dy dx =>
        let dx := df (n * (conj y)^(n-1) • dy) dx
        dx)) := by
  cases hf
  constructor
  · intro dx; fun_trans only; simp_all
    funext dy dx
    simp[revFDeriv,smul_push]; ac_rfl
  · fun_prop


@[data_synth]
theorem IndexType.sum.arg_f.HasRevFDerivUpdate
  {I : Type} [IndexType I]
  (f : W → I → X) (f' : I → _) (hz : ∀ i, HasRevFDerivUpdate R (f · i) (f' i)) :
  HasRevFDerivUpdate R
    (fun w => ∑ i, f w i)
    (fun w =>
      ((∑ i, f w i), fun dx dw =>
        IndexType.foldl (init:=dw)
          (fun dw (i : I) =>
            let' (_x,df) := f' i w
            df dx dw))) := by
  have := fun i => (hz i).val
  have : ∀ (i : I), Differentiable R fun x => f x i := fun i => (hz i).prop
  constructor
  · intro w; fun_trans[adjointFDeriv]
    sorry_proof
  · fun_prop


section OverReals

variable {R : Type} [RealScalar R]
  {W : Type} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]


@[data_synth]
theorem Inner.inner.arg_a0a1.HasRevFDerivUpdate_rule
  (f g : X → Y) (f' g')
  (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
  HasRevFDerivUpdate R
    (fun x => ⟪f x, g x⟫[R])
    (fun x =>
      let' (y,df) := f' x
      let' (z,dg) := g' x
      (⟪y,z⟫[R], fun dr dx =>
        let dx := df (conj dr • z) dx
        let dx := dg (conj dr • y) dx
        dx)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
    funext dy dx
    simp [revFDeriv,smul_push]; ac_rfl
  · fun_prop


@[data_synth]
theorem Norm2.norm2.arg_a0.HasRevFDerivUpdate_rule
  (f : X → Y) (f')
  (hf : HasRevFDerivUpdate R f f') :
  HasRevFDerivUpdate R
    (fun x => ‖f x‖₂²[R])
    (fun x =>
      let' (y,df) := f' x
      let z := ‖y‖₂²[R];
      (z, fun dr dx =>
        let dx := df ((2 * conj dr) • y) dx
        dx)) := by
  cases hf
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop

end OverReals


#exit
variable (f : X → X) (f') (hf : HasRevFDerivUpdate R f f')

#check (HasRevFDerivUpdate R (fun x => f x) _) rewrite_by data_synth

#check (HasRevFDerivUpdate R f _) rewrite_by data_synth


set_option trace.Meta.Tactic.data_synth true in
#check (HasRevFDerivUpdate R (fun x : R => x*x*x*x*x) _ )
  rewrite_by
    data_synth


#check (HasRevFDerivUpdate R (fun x : R×R => x.1 * x.2 * x.1 * x.1 * x.2) _) rewrite_by
              data_synth


#check (HasRevFDerivUpdate R (fun x : R×R => x.2 * x.1) _) rewrite_by
              data_synth


set_option trace.Meta.Tactic.data_synth true in
#check (HasRevFDerivUpdate R (fun x : R×R×R => x.1 * x.2.1) _) rewrite_by
  data_synth


set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.normalize true in
#check (HasRevFDerivUpdate R (fun x : R => let y := x; y+y) _ )
  rewrite_by
    data_synth


#check SciLean.HasRevFDerivUpdate.let_rule

set_option pp.deepTerms.threshold 1000000000000000

#check (HasRevFDerivUpdate R (fun x : R => x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x) _ )
  rewrite_by
    data_synth

#check (HasRevFDerivUpdate R (fun x : R×R×R×R => x.1) _) rewrite_by
              data_synth



set_option profiler true in
set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.normalize true in
set_option trace.Meta.Tactic.data_synth.input true in
#check (HasRevFDerivUpdate R (fun x : R =>
            let y := x * x
            let z := y * y
            z) _) rewrite_by
              data_synth


        -- (fun yx =>
        --   let z := yx.1 * yx.1;
        --   z)


set_option profiler true in
set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.normalize true in
set_option trace.Meta.Tactic.data_synth.input true in
#check (HasRevFDerivUpdate R (fun x : R =>
            let x₁ := x*x*x
            x*x₁) _) rewrite_by
              data_synth


set_option profiler true in
set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.normalize true in
set_option trace.Meta.Tactic.data_synth.input true in
#check (HasRevFDerivUpdate R (fun x : R =>
            let x₁ := x*x
            let x₂ := x*x₁
            let x₃ := x*x₂
            let x₄ := x*x₃
            x*x₄) _) rewrite_by
              data_synth



set_option profiler true in
set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.normalize true in
set_option trace.Meta.Tactic.data_synth.input true in
#check (HasRevFDerivUpdate R (fun x : R =>
            let x₁ := x*x
            let x₂ := x*x₁
            let x₃ := x*x₁*x₂
            x*x₁*x₂*x₃) _) rewrite_by
              data_synth


set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.normalize true in
set_option trace.Meta.Tactic.data_synth.input true in
#check (HasRevFDerivUpdate R (fun x : R =>
            let x₁ := x
            let x₂ := x*x₁
            x*x₁*x₂) _) rewrite_by
              data_synth

-- set_option profiler true in
-- #check (revFDeriv R (fun x : R =>
--             let x₁ := x*x
--             let x₂ := x*x₁
--             let x₃ := x*x₁*x₂
--             x*x₁*x₂*x₃) rewrite_by autodiff
set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.input true in
#check (HasRevFDerivUpdate R (fun x : R => let y := (x,x); y) _)
   rewrite_by
     data_synth


set_option profiler true in
set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.normalize true in
set_option trace.Meta.Tactic.data_synth.input true in
#check (HasRevFDerivUpdate R (fun x : R =>
            let x₁ := x*x
            let x₂ := x*x₁
            let x₃ := x*x₁*x₂
            let x₄ := x*x₁*x₂*x₃
            x*x₁*x₂*x₃*x₄) _) rewrite_by
              data_synth


set_option pp.deepTerms.threshold 100000000000000000
set_option profiler true in
-- set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.profile true in
-- set_option trace.Meta.Tactic.data_synth.normalize true in
-- set_option trace.Meta.Tactic.data_synth.input true in
#check (HasRevFDerivUpdate R (fun x : R =>
            let x₁ := x*x
            let x₂ := x*x₁
            let x₃ := x*x₁*x₂
            let x₄ := x*x₁*x₂*x₃
            let x₅ := x*x₁*x₂*x₃*x₄
            let x₆ := x*x₁*x₂*x₃*x₄*x₅
            let x₇ := x*x₁*x₂*x₃*x₄*x₅*x₆
            x*x₁*x₂*x₃*x₄*x₅*x₆*x₇) _) rewrite_by
              data_synth


#exit
set_option pp.deepTerms.threshold 10000000
#check (HasRevFDerivUpdate R (fun x : R =>
            let x₁ := x*x
            let x₂ := x*x₁
            let x₃ := x*x₁*x₂
            let x₄ := x*x₁*x₂*x₃
            x*x₁*x₂*x₃*x₄) _) rewrite_by
              data_synth



#check (HasRevFDerivUpdate R (fun x : R =>
            let x₁ := x*x
            x*x₁) _) rewrite_by
              data_synth


set_option trace.Meta.Tactic.data_synth true in
#check (HasRevFDerivUpdate R (fun x : R => let y := x * x; y * x) _ )
  rewrite_by
    data_synth



set_option trace.Meta.Tactic.simp.rewrite true in
#check (revFDeriv R (fun x : R => let x₁ := x * x; let x₂ := x*x₁; let x₃ := x*x₁*x₂; x*x₁*x₂*x₃) 2)
  rewrite_by
    simp -zeta only [dataSynthRevFDeriv]


set_option profiler true in

#check (HasRevFDerivUpdate R (fun x : R×R =>) _ 2)
  rewrite_by
    data_synth +lsimp -zeta
