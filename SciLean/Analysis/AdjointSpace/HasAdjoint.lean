import SciLean.Analysis.AdjointSpace.Adjoint
import SciLean.Tactic.DataSynth.Attr
import SciLean.Tactic.DataSynth.Elab
import SciLean.Tactic.DataSynth.DefDataSynth
import SciLean.Meta.Notation.Let'
import SciLean.Lean.Meta.Basic

variable
  {K : Type u'} [RCLike K]
  {X : Type u} [NormedAddCommGroup X] [AdjointSpace K X]
  {Y : Type v} [NormedAddCommGroup Y] [AdjointSpace K Y]
  {Z : Type w} [NormedAddCommGroup Z] [AdjointSpace K Z]

namespace SciLean

open Lean

variable (K)
@[data_synth out f' in f]
structure HasAdjoint (f : X → Y) (f' : Y → X) : Prop where
  adjoint : ∀ x y, ⟪f x, y⟫[K] = ⟪x, f' y⟫[K]
  is_linear : IsContinuousLinearMap K f

@[data_synth out f' in f]
structure HasAdjointUpdate (f : X → Y) (f' : Y → X → X) : Prop where
  adjoint : ∀ (x' : X) x y, ⟪f x, y⟫[K] = ⟪x, f' y x'⟫[K] - ⟪x, x'⟫[K]
  is_linear : IsContinuousLinearMap K f
variable {K}

theorem hasAdjointUpdate_eq_hasAdjoint_add (f : X → Y) {f' f''}
    (hf : HasAdjoint K f f') (hf' : HasAdjointUpdate K f f'') :
    f'' y x = f' y + x := by
  apply AdjointSpace.ext_inner_left K
  intro x'
  calc _ = (⟪x', f'' y x⟫[K] - ⟪x', x⟫[K]) + ⟪x',x⟫[K] := by ring
       _ = ⟪f x', y⟫[K] + ⟪x', x⟫[K] := by rw[← hf'.adjoint x]
       _ = _ := by rw[hf.adjoint]; rw[AdjointSpace.inner_add_right]

theorem HasAdjointUpdate.adjoint' {f : X → Y} {f' : Y → X → X} (h : HasAdjointUpdate K f f') :
  ∀ x yx, ⟪(f x, x), yx⟫[K] = ⟪x, f' yx.1 yx.2⟫[K] := by
  intro x y
  simp_rw[AdjointSpace.inner_prod_split]
  rw[h.adjoint y.2]
  ring

set_option linter.unusedVariables false in
theorem HasAdjointUpdate.apply_eq_zero_add {f : X → Y} {f' : Y → X → X}
    (h : HasAdjointUpdate K f f') (x y) :
    f' y x = f' y 0 + x := by
  apply AdjointSpace.ext_inner_left K
  intro x'
  sorry_proof

set_option linter.unusedVariables false in
theorem HasAdjointUpdate.smul_left {f : X → Y} {f' : Y → X → X}
    (h : HasAdjointUpdate K f f') (x y) (k : K) :
    f' (k•y) x = k•f' y x - k•x + x  := by
  apply AdjointSpace.ext_inner_left K
  intro x'
  sorry_proof

theorem hasAdjointUpdate_from_hasAdjoint {f : X → Y} {f' : Y → X} {f'' : Y → X → X}
    (adjoint : HasAdjoint K f f') (simp : ∀ y x, f'' y x = x + f' y) :
    HasAdjointUpdate K f f'' := by
  constructor
  case adjoint => intro x' x y; simp[adjoint.adjoint,simp,AdjointSpace.inner_add_right]
  case is_linear => have := adjoint.is_linear; fun_prop

set_option linter.unusedVariables false in
theorem HasAdjoint.isContinuousLinearMap {f : X → Y} {f' : Y → X} (hf : HasAdjoint K f f') :
    IsContinuousLinearMap K f := sorry_proof

set_option linter.unusedVariables false in
theorem HasAdjoint.isContinuousLinearMap' {f : X → Y} {f' : Y → X} (hf : HasAdjoint K f f') :
    IsContinuousLinearMap K f' := sorry_proof

theorem HasAdjointUpdate.hasAdjoint {f : X → Y} {f' : Y → X → X}
    (h : HasAdjointUpdate K f f') :
    HasAdjoint K f (f' · 0) := by
  constructor
  · intros; rw[h.adjoint (x':=0)]; simp
  · apply h.is_linear


set_option linter.unusedVariables false in
-- @[to_data_synth_simproc] -- this attribute should automatically generate the following simproc
theorem adjoint_from_hasAdjoint
  {f : X → Y} {f'} (hf : HasAdjoint K f f') :
  adjoint K f = f' := sorry_proof

simproc_decl adjoint_simproc (adjoint _ _) :=
  mkDataSynthSimproc `adjoint_simproc ``adjoint_from_hasAdjoint

variable (K) in
noncomputable
def adjointUpdate (f : X → Y) (y : Y) (x : X) : X := x + adjoint K f y

set_option linter.unusedVariables false in
-- @[to_data_synth_simproc] -- this attribute should automatically generate the following simproc
theorem adjointUpdate_from_hasAdjointUpdate
  {f : X → Y} {f'} (hf : HasAdjointUpdate K f f') :
  adjointUpdate K f = f' := sorry_proof

simproc_decl adjointUpdate_simproc (adjointUpdate _ _) :=
  mkDataSynthSimproc `adjointUpdate_simproc ``adjointUpdate_from_hasAdjointUpdate


namespace HasAdjoint

@[data_synth]
theorem id_rule : HasAdjoint K (fun x : X => x) (fun x => x) := by
  constructor
  case adjoint => simp
  case is_linear => fun_prop

theorem const_rule : HasAdjoint K (fun _ : X => (0 : Y)) (fun _ => 0) := by
  constructor
  case adjoint => simp
  case is_linear => fun_prop

theorem comp_rule (g : X → Y) (f : Y → Z) {g' f'}
    (hg : HasAdjoint K g g') (hf : HasAdjoint K f f') :
    HasAdjoint K
      (fun x => f (g x))
      (fun z =>
        let y := f' z
        let x := g' y
        x) := by
  constructor
  case adjoint => intro x y; simp_rw [hf.adjoint,hg.adjoint]
  case is_linear => have := hg.is_linear; have := hf.is_linear; fun_prop

theorem let_rule (g : X → Y) (f : Y → X → Z) {g' f'}
    (hg : HasAdjointUpdate K g g') (hf : HasAdjoint K (fun yx : Y×X => f yx.1 yx.2) f') :
    HasAdjoint K
      (fun x =>
        let y := g x
        f y x)
      (fun z =>
        let' (y,x) := f' z
        let x := g' y x
        x) := by
  constructor
  case adjoint =>
    intro x z; dsimp
    have h := hf.adjoint ((g x),x) z; simp at h; rw[h]
    rw[hg.adjoint']
  case is_linear => have := hg.is_linear; have := hf.is_linear; fun_prop


theorem pi_rule {I : Type*} {n} [IndexType I n] [Fold.{_,u'} I] [Fold.{_,u} I]
    (f : X → I → Y) {f' : I → _} (hf : ∀ i, HasAdjointUpdate K (f · i) (f' i)) :
    HasAdjoint K
      (fun x i => f x i)
      (fun y =>
        IndexType.fold .full (init:=(0:X)) fun i x =>
          let yi := y i
          let x := f' i yi x
          x) := by
  constructor
  case adjoint =>
    intro x y
    have h := fun i => (hf i).adjoint 0
    simp[Inner.inner, h]
    sorry_proof
  case is_linear => apply IsContinuousLinearMap.pi_rule _ (fun i => (hf i).is_linear)



set_option linter.unusedVariables false in
theorem proj_rule
    {X₁ : Type*} [NormedAddCommGroup X₁] [AdjointSpace K X₁]
    {X₂ : Type*} [NormedAddCommGroup X₂] [AdjointSpace K X₂]
    (f : X → Y) (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) {g'}
    (hg : HasAdjoint K g g') :
    HasAdjoint K f (fun y =>
      let x₁ := g' y
      let x := q x₁ 0
      x) := sorry_proof


open Lean Meta
#eval show MetaM Unit from do
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasAdjoint,``const_rule⟩, .const⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasAdjoint, ``comp_rule⟩, .comp
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f)
      (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasAdjoint,``let_rule⟩, .letE
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f)
      (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasAdjoint,``pi_rule⟩, .pi
      (← getConstArgId ``pi_rule `f) (← getConstArgId ``pi_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasAdjoint,``proj_rule⟩, .proj
      (← getConstArgId ``proj_rule `f) (← getConstArgId ``proj_rule `g)
      (← getConstArgId ``proj_rule `p₁) (← getConstArgId ``proj_rule `p₂)
      (← getConstArgId ``proj_rule `q) (← getConstArgId ``proj_rule `hg)⟩

end HasAdjoint

namespace HasAdjointUpdate

@[data_synth]
theorem id_rule : HasAdjointUpdate K (fun x : X => x) (fun x x' => x' + x) := by
  constructor
  case adjoint => simp[AdjointSpace.inner_add_right]
  case is_linear => fun_prop

theorem const_rule : HasAdjointUpdate K (fun _ : X => (0 : Y)) (fun _ x => x) := by
  constructor
  case adjoint => simp
  case is_linear => fun_prop

theorem comp_rule (g : X → Y) (f : Y → Z) {g' f'}
    (hg : HasAdjointUpdate K g g') (hf : HasAdjoint K f f') :
    HasAdjointUpdate K
      (fun x => f (g x))
      (fun z x =>
        let y := f' z
        let x := g' y x
        x) := by
  constructor
  case adjoint => intro x y; simp [hf.adjoint,hg.adjoint x]
  case is_linear => have := hg.is_linear; have := hf.is_linear; fun_prop

theorem let_rule (g : X → Y) (f : Y → X → Z) {g' f'}
    (hg : HasAdjointUpdate K g g') (hf : HasAdjointUpdate K (fun yx : Y×X => f yx.1 yx.2) f') :
    HasAdjointUpdate K
      (fun x =>
        let y := g x
        f y x)
      (fun z x =>
        let' (y,x) := f' z (0,x)
        let x := g' y x
        x) := by
  constructor
  case adjoint =>
    intro x' x z; dsimp
    have h := hf.adjoint (0,x') ((g x),x) z; simp at h; rw[h]
    rw[hg.adjoint']
    simp[AdjointSpace.inner_prod_split]
  case is_linear => have := hg.is_linear; have := hf.is_linear; fun_prop

theorem pi_rule {I : Type*} {n} [IndexType I n] [Fold.{_,u'} I] [Fold.{_,u} I]
    (f : X → I → Y) {f' : I → _} (hf : ∀ i, HasAdjointUpdate K (f · i) (f' i)) :
    HasAdjointUpdate K
      (fun x i => f x i)
      (fun y x =>
        IndexType.fold .full (init:=x) fun i x =>
          let yi := y i
          let x := f' i yi x
          x) := by
  constructor
  case adjoint =>
    intro x y
    have h := fun i => (hf i).adjoint
    simp[Inner.inner, h]
    sorry_proof
  case is_linear => apply IsContinuousLinearMap.pi_rule _ (fun i => (hf i).is_linear)

set_option linter.unusedVariables false in
theorem proj_rule
    {X₁ : Type*} [NormedAddCommGroup X₁] [AdjointSpace K X₁]
    {X₂ : Type*} [NormedAddCommGroup X₂] [AdjointSpace K X₂]
    (f : X → Y) (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) {g'}
    (hg : HasAdjointUpdate K g g') :
    HasAdjointUpdate K f
      (fun y x =>
        let x₁ := p₁ x
        let x₂ := p₂ x
        let x₁ := (g' y x₁)
        let x := q x₁ x₂
        x) := sorry_proof

open Lean Meta
#eval show MetaM Unit from do
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasAdjointUpdate,``const_rule⟩, .const⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasAdjointUpdate, ``comp_rule⟩, .comp
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f)
      (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasAdjointUpdate,``let_rule⟩, .letE
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f)
      (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasAdjointUpdate,``pi_rule⟩, .pi
      (← getConstArgId ``pi_rule `f) (← getConstArgId ``pi_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasAdjointUpdate,``proj_rule⟩, .proj
      (← getConstArgId ``proj_rule `f) (← getConstArgId ``proj_rule `g)
      (← getConstArgId ``proj_rule `p₁) (← getConstArgId ``proj_rule `p₂)
      (← getConstArgId ``proj_rule `q) (← getConstArgId ``proj_rule `hg)⟩

end HasAdjointUpdate

end SciLean
open SciLean

@[data_synth]
theorem Prod.mk.arg_a0a1.HasAdjoint_comp_rule (f : X → Y) (g : X → Z)
  (hf : HasAdjoint K f f') (hg : HasAdjointUpdate K g g') :
  HasAdjoint K
    (fun x => (f x, g x))
    (fun yz =>
      let' (y,z) := yz
      g' z (f' y)) := by
  constructor
  case adjoint =>
    intro x y
    simp[AdjointSpace.inner_prod_split,hf.adjoint,hg.adjoint (f' y.1)]
  case is_linear => have := hf.is_linear; have := hg.is_linear; fun_prop

-- reverse version of the previous theorem, not sure which one is better
theorem Prod.mk.arg_a0a1.HasAdjoint_rule' (f : X → Y) (g : X → Z)
  (hf : HasAdjointUpdate K f f') (hg : HasAdjoint K g g') :
  HasAdjoint K
    (fun x => (f x, g x))
    (fun yz =>
      let' (y,z) := yz
      f' y (g' z)) := by
  constructor
  case adjoint =>
    intro x y;
    simp[AdjointSpace.inner_prod_split,hg.adjoint,hf.adjoint (g' y.2)]
  case is_linear => have := hf.is_linear; have := hg.is_linear; fun_prop

@[data_synth]
theorem Prod.mk.arg_a0a1.HasAdjointUpdate_comp_rule (f : X → Y) (g : X → Z)
  (hf : HasAdjointUpdate K f f') (hg : HasAdjointUpdate K g g') :
  HasAdjointUpdate K
    (fun x => (f x, g x))
    (fun yz x =>
      let' (y,z) := yz
      g' z (f' y x)) := by
  constructor
  case adjoint =>
    intro x' x y
    simp[AdjointSpace.inner_prod_split,hf.adjoint x',hg.adjoint (f' y.1 x')]
  case is_linear => have := hf.is_linear; have := hg.is_linear; fun_prop

@[data_synth]
theorem Prod.fst.arg_self.HasAdjoint_simple_rule :
    HasAdjoint K (fun xy : X×Y => xy.1) (fun x => (x,0)) := by
  constructor
  case adjoint => simp[AdjointSpace.inner_prod_split]
  case is_linear => fun_prop

@[data_synth]
theorem Prod.fst.arg_self.HasAdjointUpdate_simple_rule :
    HasAdjointUpdate K
      (fun xy : X×Y => xy.1)
      (fun x xy =>
        let' (x',y') := xy
        (x' + x, y')) := by
  constructor
  case adjoint => simp[AdjointSpace.inner_prod_split, AdjointSpace.inner_add_right]
  case is_linear => fun_prop

@[data_synth]
theorem Prod.snd.arg_self.HasAdjoint_simple_rule :
    HasAdjoint K (fun xy : X×Y => xy.2) (fun y => (0,y)) := by
  constructor
  case adjoint => simp[AdjointSpace.inner_prod_split]
  case is_linear => fun_prop

@[data_synth]
theorem Prod.snd.arg_self.HasAdjointUpdate_simple_rule :
    HasAdjointUpdate K
      (fun xy : X×Y => xy.2)
      (fun y xy =>
        let' (x',y') := xy
        (x', y' + y)) := by
  constructor
  case adjoint => simp[AdjointSpace.inner_prod_split, AdjointSpace.inner_add_right]
  case is_linear => fun_prop

@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasAdjoint_simple_rule :
    HasAdjoint K
      (fun x : X×X => x.1 + x.2)
      (fun x => (x,x)) := by
  constructor
  case adjoint => simp[AdjointSpace.inner_prod_split, AdjointSpace.inner_add_left, AdjointSpace.inner_add_right]
  case is_linear => fun_prop

@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasAdjointUpdate_simple_rule :
    HasAdjointUpdate K
      (fun x : X×X => x.1 + x.2)
      (fun x x' =>
         let' (x'₁, x'₂) := x'
         (x'₁ + x, x'₂ + x)) := by
  constructor
  case adjoint => simp[AdjointSpace.inner_prod_split, AdjointSpace.inner_add_left, AdjointSpace.inner_add_right]; ring_nf; simp
  case is_linear => fun_prop

@[data_synth]
theorem HSub.hSub.arg_a0a1.HasAdjoint_simple_rule :
    HasAdjoint K
      (fun x : X×X => x.1 - x.2)
      (fun x => (x, -x)) := by
  constructor
  case adjoint => simp[AdjointSpace.inner_prod_split, AdjointSpace.inner_add_left, AdjointSpace.inner_add_right,sub_eq_add_neg]
  case is_linear => fun_prop

@[data_synth]
theorem HSub.hSub.arg_a0a1.HasAdjointUpdate_simple_rule :
    HasAdjointUpdate K
      (fun x : X×X => x.1 - x.2)
      (fun x x' =>
         let' (x'₁, x'₂) := x'
         (x'₁ + x, x'₂ - x)) := by
  constructor
  case adjoint =>
    simp[AdjointSpace.inner_prod_split, AdjointSpace.inner_add_left,
         AdjointSpace.inner_add_right,sub_eq_add_neg]; ring_nf; simp
  case is_linear => fun_prop

@[data_synth]
theorem Neg.neg.arg_a0.HasAdjoint_simple_rule :
    HasAdjoint K
      (fun x : X => -x)
      (fun x => -x) := by
  constructor
  case adjoint => simp
  case is_linear => fun_prop

@[data_synth]
theorem Neg.neg.arg_a0.HasAdjointUpdate_simple_rule :
    HasAdjointUpdate K
      (fun x : X => -x)
      (fun x x' => x' - x) := by
  constructor
  case adjoint => simp[AdjointSpace.inner_add_right,sub_eq_add_neg]
  case is_linear => fun_prop

@[data_synth]
theorem HSmul.hSMul.arg_a0.HasAdjoint_simp_rule (x : X) :
    HasAdjoint K
      (fun k : K => k • x)
      (fun y => ⟪x,y⟫[K]) := by
  constructor
  case adjoint => intro k y; simp [AdjointSpace.inner_smul_left,mul_comm]
  case is_linear => sorry_proof

@[data_synth]
theorem HSmul.hSMul.arg_a0.HasAdjointUpdate_simp_rule (x : X) :
    HasAdjointUpdate K
      (fun k : K => k • x)
      (fun y k => k + ⟪x,y⟫[K]) := by
  constructor
  case adjoint => intro k y; simp [AdjointSpace.inner_smul_left]; ring_nf; simp
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HSMul.hSMul.arg_a1.HasAdjoint_simple_rule (k : K) :
    HasAdjoint K
      (fun x : X => k • x)
      (fun x => conj k • x) := by
  constructor
  case adjoint => intro x y; simp [AdjointSpace.inner_smul_left,AdjointSpace.inner_smul_right]
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HSMul.hSMul.arg_a1.HasAdjointUpdate_simple_rule (k : K) :
    HasAdjointUpdate K
      (fun x : X => k • x)
      (fun x x' => x' + conj k • x) := by
  constructor
  case adjoint =>
    intro x y;
    simp [AdjointSpace.inner_smul_left,AdjointSpace.inner_smul_right,AdjointSpace.inner_add_right]
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HSMul.hSMul.arg_a1.HasAdjoint_simple_rule_nat (n : ℕ) :
    HasAdjoint K
      (fun x : X => n • x)
      (fun x => n • x) := by
  constructor
  case adjoint =>
    intro x y;
    simp [← Nat.cast_smul_eq_nsmul (R:=K),AdjointSpace.inner_smul_left,
          AdjointSpace.inner_smul_right,AdjointSpace.inner_add_right]
  case is_linear =>
    simp [← Nat.cast_smul_eq_nsmul (R:=K)]; fun_prop

open ComplexConjugate in
@[data_synth]
theorem HSMul.hSMul.arg_a1.HasAdjointUpdate_simple_rule_nat (n : ℕ) :
    HasAdjointUpdate K
      (fun x : X => n • x)
      (fun x x' => x' + n • x) := by
  constructor
  case adjoint =>
    intros x y
    simp [← Nat.cast_smul_eq_nsmul (R:=K),AdjointSpace.inner_smul_left,
          AdjointSpace.inner_smul_right,AdjointSpace.inner_add_right]
  case is_linear =>
    simp [← Nat.cast_smul_eq_nsmul (R:=K)]; fun_prop

  @[data_synth]
  theorem HSMul.hSMul.arg_a1.HasAdjoint_simple_rule_int (n : Int) :
    HasAdjoint K
      (fun x : X => n • x)
      (fun x => n • x) := by
    constructor
    case adjoint =>
      intro x y;
      simp [← Int.cast_smul_eq_zsmul (R:=K),AdjointSpace.inner_smul_left,
            AdjointSpace.inner_smul_right,AdjointSpace.inner_add_right]
    case is_linear =>
      simp [← Int.cast_smul_eq_zsmul (R:=K)]; fun_prop

  @[data_synth]
  theorem HSMul.hSMul.arg_a1.HasAdjointUpdate_simple_rule_int (n : Int) :
    HasAdjointUpdate K
      (fun x : X => n • x)
      (fun x x' => x' + n • x) := by
    constructor
    case adjoint =>
      intro x y;
      simp [← Int.cast_smul_eq_zsmul (R:=K),AdjointSpace.inner_smul_left,
            AdjointSpace.inner_smul_right,AdjointSpace.inner_add_right]
    case is_linear =>
      simp [← Int.cast_smul_eq_zsmul (R:=K)]; fun_prop

-- todo: finish the proof as I'm not sure if these assumptions are sufficient!!! (but very plausible)
open ComplexConjugate in
@[data_synth]
theorem HSMul.hSMul.arg_a1.HasAdjoint_simple_rule_complex_over_real
    {R} [RealScalar R] {K} [RCLike K] [Algebra R K]
    {X} [NormedAddCommGroup X] [AdjointSpace R X] [AdjointSpace K X] [IsScalarTower R K X]
    (k : K) :
    HasAdjoint R
      (fun x : X => k • x)
      (fun x => (conj k) • x) := by
  constructor
  case adjoint => intro y z; sorry_proof
  case is_linear => sorry_proof

-- todo: finish the proof as I'm not sure if these assumptions are sufficient!!! (but very plausible)
open ComplexConjugate in
@[data_synth]
theorem HSMul.hSMul.arg_a1.HasAdjointUpdate_simple_rule_complex_over_real
    {R} [RealScalar R] {K} [RCLike K] [Algebra R K]
    {X} [NormedAddCommGroup X] [AdjointSpace R X] [AdjointSpace K X] [IsScalarTower R K X]
    (k : K) :
    HasAdjointUpdate R
      (fun x : X => k • x)
      (fun x x'=> x' + (conj k) • x) := by
  constructor
  case adjoint => intro y z; sorry_proof
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HMul.hMul.arg_a0.HasAdjoint_simp_rule (y : K) :
    HasAdjoint K
      (fun x => x * y)
      (fun z => z * conj y) := by
  constructor
  case adjoint => intro k y; simp; ac_rfl
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HMul.hMul.arg_a0.HasAdjointUpdate_simp_rule (y : K) :
    HasAdjointUpdate K
      (fun x => x * y)
      (fun z x' => x' + z * conj y) := by
  constructor
  case adjoint => intro k y; simp; ring_nf; simp
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HMul.hMul.arg_a1.HasAdjoint_simp_rule (x : K) :
    HasAdjoint K
      (fun y => x * y)
      (fun z => conj x * z) := by
  constructor
  case adjoint => intro k y; simp; ac_rfl
  case is_linear => sorry_proof

set_option linter.unusedVariables false in
open ComplexConjugate in
@[data_synth]
theorem HMul.hMul.arg_a1.HasAdjoint_comp_rule
    (y : K) (f : X → K) {f'} (hf : HasAdjoint K f f') :
    HasAdjoint K
      (fun x => y * f x)
      (fun z =>
        let x := f' z
        conj y • x) := by
  constructor
  case adjoint => intro k y; sorry_proof
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HMul.hMul.arg_a1.HasAdjointUpdate_simp_rule (x : K) :
    HasAdjointUpdate K
      (fun y => x * y)
      (fun z y' => y' + conj x * z) := by
  constructor
  case adjoint => intro k y; simp; ring_nf; simp
  case is_linear => sorry_proof

set_option linter.unusedVariables false in
open ComplexConjugate in
@[data_synth]
theorem HMul.hMul.arg_a1.HasAdjointUpdate_comp_rule
    (y : K) (f : X → K) {f'} (hf : HasAdjointUpdate K f f') :
    HasAdjointUpdate K
      (fun x => y * f x)
      (fun z y' =>
        let x := f' (conj y • z) y'
        x) := by
  constructor
  case adjoint => intro k y; dsimp; sorry_proof
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HDiv.hDiv.arg_a0.HasAdjoint_simp_rule (y : K) :
    HasAdjoint K
      (fun x => x / y)
      (fun z => z / conj y) := by
  constructor
  case adjoint => intro k y; simp; ring
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HDiv.hDiv.arg_a0.HasAdjointUpdate_simp_rule (y : K) :
    HasAdjointUpdate K
      (fun x => x / y)
      (fun z x' => x' + z / conj y) := by
  constructor
  case adjoint => intro k y; simp; ring_nf; simp
  case is_linear => sorry_proof

@[data_synth]
theorem SciLean.IndexType.sum.arg_f.HasAdjoint_simp_rule
    {I : Type*} {n} [IndexType I n] [Fold.{_,u'} I] [Fold.{_,u} I] :
    HasAdjoint K
      (fun f : I → X => ∑ᴵ i, f i)
      (fun k _ => k) := by
  constructor
  case adjoint => intro f y; simp[Inner.inner]; sorry_proof -- missing API
  case is_linear => fun_prop

-- we have to formulate it this way too because some issue with RefinedDiscrTree
-- once mathlib PR #11968 is merges this should not be necessaryx
@[data_synth]
theorem SciLean.IndexType.sum.arg_f.HasAdjoint_simp_rule'
    {I : Type*} {n} [IndexType I n] [Fold.{_,u'} I] [Fold.{_,u} I] :
    HasAdjoint K
      (fun f : I → X => IndexType.sum f)
      (fun k _ => k) := SciLean.IndexType.sum.arg_f.HasAdjoint_simp_rule

@[data_synth]
theorem SciLean.IndexType.sum.arg_f.HasAdjointUpdate_simp_rule
    {I : Type*} {n} [IndexType I n] [Fold.{_,u'} I] [Fold.{_,u} I] :
    HasAdjointUpdate K
      (fun f : I → X => ∑ᴵ i, f i)
      (fun k f' i => f' i + k) := by
  constructor
  case adjoint => intro f y; simp[Inner.inner]; sorry_proof -- missing API
  case is_linear => fun_prop

-- we have to formulate it this way too because some issue with RefinedDiscrTree
-- once mathlib PR #11968 is merges this should not be necessaryx
@[data_synth]
theorem SciLean.IndexType.sum.arg_f.HasAdjointUpdate_simp_rule'
    {I : Type*} {n} [IndexType I n] [Fold.{_,u'} I] [Fold.{_,u} I] :
    HasAdjointUpdate K
      (fun f : I → X => sum f)
      (fun k f' i => f' i + k) := SciLean.IndexType.sum.arg_f.HasAdjointUpdate_simp_rule

@[data_synth]
theorem Finset.sum.arg_f.HasAdjoint_simp_rule
    {I : Type*} {n} [IndexType I n] [Fold.{_,u'} I]
    (A : Finset I) :
    HasAdjoint K
      (fun f : I → X => A.sum (fun i => f i))
      (fun k i => A.toSet.indicator (fun _ => k) i) := by
  constructor
  case adjoint => intro f y; simp[Inner.inner]; sorry_proof -- missing API
  case is_linear => fun_prop

-- we have to formulate it this way too because some issue with RefinedDiscrTree
-- once mathlib PR #11968 is merges this should not be necessaryx
@[data_synth]
theorem Finset.sum.arg_f.HasAdjoint_simp_rule'
    {I : Type*} {n} [IndexType I n] [Fold.{_,u'} I]
    (A : Finset I) :
    HasAdjoint K
      (fun f : I → X => A.sum f)
      (fun k i => A.toSet.indicator (fun _ => k) i) := by
  constructor
  case adjoint => intro f y; simp[Inner.inner]; sorry_proof -- missing API
  case is_linear => fun_prop

@[data_synth]
theorem Finset.sum.arg_f.HasAdjointUpdate_simp_rule
    {I : Type*} {n} [IndexType I n] [Fold.{_,u'} I]
    (A : Finset I) :
    HasAdjointUpdate K
      (fun f : I → X => A.sum (fun i => f i))
      (fun k f i => f i + A.toSet.indicator (fun _ => k) i) := by
  constructor
  case adjoint => intro f y; simp[Inner.inner]; sorry_proof -- missing API
  case is_linear => fun_prop

-- we have to formulate it this way too because some issue with RefinedDiscrTree
-- once mathlib PR #11968 is merges this should not be necessaryx
@[data_synth]
theorem Finset.sum.arg_f.HasAdjointUpdate_simp_rule'
    {I : Type*} {n} [IndexType I n] [Fold.{_,u'} I]
    (A : Finset I) :
    HasAdjointUpdate K
      (fun f : I → X => A.sum f)
      (fun k f i => f i + A.toSet.indicator (fun _ => k) i) := by
  constructor
  case adjoint => intro f y; simp[Inner.inner]; sorry_proof -- missing API
  case is_linear => fun_prop


@[data_synth]
theorem ite.arg_te.HasAdjoint_simple_rule {c : Prop} [Decidable c] :
    HasAdjoint K
      (fun te : X×X => if c then te.1 else te.2)
      (fun y => if c then (y,0) else (0,y)) := by
  constructor
  case adjoint => intro x y; split_ifs <;> simp[AdjointSpace.inner_prod_split]
  case is_linear => fun_prop

@[data_synth]
theorem ite.arg_te.HasAdjointUpdate_simple_rule {c : Prop} [Decidable c] :
    HasAdjointUpdate K
      (fun te : X×X => if c then te.1 else te.2)
      (fun y te =>
        let' (t,e) := te
        if c then (t + y,e) else (t,e + y)) := by
  constructor
  case adjoint =>
    intro x y
    split_ifs <;> simp[AdjointSpace.inner_prod_split,AdjointSpace.inner_add_right]
  case is_linear => fun_prop

open ComplexConjugate in
@[data_synth]
theorem Inner.inner.arg_a0.HasAdjoint_simple_rule_real
    {R K} [RealScalar R] [Scalar R K] [ScalarSMul R K] [ScalarInner R K]
    {X} [NormedAddCommGroup X] [AdjointSpace R X] [AdjointSpace K X]
    -- add some condition that connects inner product over R and K
    --   ∀ (x y : X), Scalar.real ⟪x,y⟫[K] = ⟪x,y⟫[R]
    (y : X) :
    HasAdjoint R
      (fun x : X => ⟪x,y⟫[K])
      (fun k => (conj k)•y) := by
  constructor
  case adjoint =>
    intro x k
    simp[AdjointSpace.inner_smul_right,ScalarInner.inner_eq_inner_re_im]
    -- lhs has complex inner product and rhs has real inner product
    -- it should work out
    sorry_proof
  case is_linear => fun_prop

open ComplexConjugate in
@[data_synth]
theorem Inner.inner.arg_a0.HasAdjointUpdate_simple_rule_real
    {R K} [RealScalar R] [Scalar R K] [ScalarSMul R K] [ScalarInner R K]
    {X} [NormedAddCommGroup X] [AdjointSpace R X] [AdjointSpace K X]
    (y : X) :
    HasAdjointUpdate R
      (fun x : X => ⟪x,y⟫[K])
      (fun k x => x + (conj k)•y) := by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => simp

@[data_synth]
theorem Inner.inner.arg_a1.HasAdjoint_simple_rule (x : X) :
    HasAdjoint K
      (fun y : X => ⟪x,y⟫[K])
      (fun k => k • x) := by
  constructor
  case adjoint => intro y z; simp[AdjointSpace.inner_smul_right]
  case is_linear => fun_prop

@[data_synth]
theorem Inner.inner.arg_a1.HasAdjoint_simple_rule_real
    {R K} [RealScalar R] [Scalar R K] [ScalarSMul R K] [ScalarInner R K]
    {X} [NormedAddCommGroup X] [AdjointSpace R X] [AdjointSpace K X]
    (x : X) :
    HasAdjoint R
      (fun y : X => ⟪x,y⟫[K])
      (fun k => k • x) := by
  constructor
  case adjoint => intro y z;  simp[ScalarInner.inner_eq_inner_re_im]; sorry_proof
  case is_linear => fun_prop


@[data_synth]
theorem Inner.inner.arg_a1.HasAdjointUpdate_simple_rule (x : X) :
    HasAdjointUpdate K
      (fun y : X => ⟪x,y⟫[K])
      (fun k x' => x' + k • x) := by
  constructor
  case adjoint =>
    intro y z; simp[AdjointSpace.inner_smul_right, AdjointSpace.inner_add_right]
  case is_linear => fun_prop

@[data_synth]
theorem Inner.inner.arg_a1.HasAdjointUpdate_simple_rule_real
    {R K} [RealScalar R] [Scalar R K] [ScalarSMul R K] [ScalarInner R K]
    {X} [NormedAddCommGroup X] [AdjointSpace R X] [AdjointSpace K X]
    (x : X) :
    HasAdjointUpdate R
      (fun y : X => ⟪x,y⟫[K])
      (fun k y => y + k • x) := by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => simp
