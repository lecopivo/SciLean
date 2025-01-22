import SciLean.Analysis.AdjointSpace.Adjoint
import SciLean.Tactic.DataSynth.Attr
import SciLean.Tactic.DataSynth.Elab
import SciLean.Meta.Notation.Let'

variable
  {K : Type*} [RCLike K]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace K X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace K Y]
  {Z : Type*} [NormedAddCommGroup Z] [AdjointSpace K Z]

namespace SciLean

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


set_default_scalar K

theorem hasAdjointUpdate_eq_hasAdjoint_add (f : X → Y) {f' f''}
    (hf : HasAdjoint K f f') (hf' : HasAdjointUpdate K f f'') :
    f'' y x = f' y + x := by
  apply AdjointSpace.ext_inner_left K
  intro x'
  calc _ = (⟪x', f'' y x⟫ - ⟪x', x⟫) + ⟪x',x⟫ := by ring
       _ = ⟪f x', y⟫ + ⟪x', x⟫ := by rw[← hf'.adjoint x]
       _ = _ := by rw[hf.adjoint]; rw[AdjointSpace.inner_add_right]

theorem HasAdjointUpdate.adjoint' {f : X → Y} {f' : Y → X → X} (h : HasAdjointUpdate K f f') :
  ∀ x yx, ⟪(f x, x), yx⟫[K] = ⟪x, f' yx.1 yx.2⟫[K] := by
  intro x y
  simp_rw[AdjointSpace.inner_prod_split]
  rw[h.adjoint y.2]
  ring


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
    HasAdjoint K (fun x => f (g x)) (fun z => g' (f' z)) := by
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
        g' y x) := by
  constructor
  case adjoint =>
    intro x z; dsimp
    have h := hf.adjoint ((g x),x) z; simp at h; rw[h]
    rw[hg.adjoint']
  case is_linear => have := hg.is_linear; have := hf.is_linear; fun_prop

theorem pi_rule {I : Type*} [IndexType I]
    (f : X → I → Y) {f' : I → _} (hf : ∀ i, HasAdjointUpdate K (f · i) (f' i)) :
    HasAdjoint K
      (fun x i => f x i)
      (fun y =>
        IndexType.foldl (init:=(0:X)) fun x i => f' i (y i) x) := by
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
    HasAdjoint K f (fun y => q (g' y) 0) := sorry_proof

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
    HasAdjointUpdate K (fun x => f (g x)) (fun z => g' (f' z)) := by
  constructor
  case adjoint => intro x y; simp [hf.adjoint,hg.adjoint x]
  case is_linear => have := hg.is_linear; have := hf.is_linear; fun_prop

theorem let_rule (g : X → Y) (f : Y → X → Z) {g' f'}
    (hg : HasAdjointUpdate K g g') (hf : HasAdjointUpdate K (fun yx : Y×X => f yx.1 yx.2) f') :
    HasAdjointUpdate K
      (fun x =>
        let y := g x
        f y x)
      (fun z x=>
        let' (y,x) := f' z (0,x)
        g' y x) := by
  constructor
  case adjoint =>
    intro x' x z; dsimp
    have h := hf.adjoint (0,x') ((g x),x) z; simp at h; rw[h]
    rw[hg.adjoint']
    simp[AdjointSpace.inner_prod_split]
  case is_linear => have := hg.is_linear; have := hf.is_linear; fun_prop

theorem pi_rule {I : Type*} [IndexType I]
    (f : X → I → Y) {f' : I → _} (hf : ∀ i, HasAdjointUpdate K (f · i) (f' i)) :
    HasAdjointUpdate K
      (fun x i => f x i)
      (fun y x =>
        IndexType.foldl (init:=x) fun x i => f' i (y i) x) := by
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
        q (g' y x₁) x₂) := sorry_proof

end HasAdjointUpdate

end SciLean
open SciLean

@[data_synth]
theorem Prod.mk.arg_a0a1.HasAdjoint_rule (f : X → Y) (g : X → Z)
  (hf : HasAdjoint K f f') (hg : HasAdjointUpdate K g g') :
  HasAdjoint K
    (fun x => (f x, g x))
    (fun yz =>
      let' (y,z) := yz
      g' z (f' y)) := by
  constructor
  case adjoint =>
    intro x y;
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
theorem Prod.mk.arg_a0a1.HasAdjointUpdate_rule (f : X → Y) (g : X → Z)
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
theorem HAdd.hAdd.arg_a0a1.HasAdjoint_rule (f g : X → Y) {f' g'}
    (hf : HasAdjoint K f f') (hg : HasAdjointUpdate K g g') :
    HasAdjoint K
      (fun x => f x + g x)
      (fun y => g' y (f' y)) := by
  constructor
  case adjoint => intro x y; simp [AdjointSpace.inner_add_left,hf.adjoint,hg.adjoint (f' y)]
  case is_linear => have := hf.is_linear; have := hg.is_linear; fun_prop


@[data_synth]
theorem HSub.hSub.arg_a0a1.HasAdjoint_rule (f g : X → Y) {f' g'}
    (hf : HasAdjoint K f f') (hg : HasAdjointUpdate K g g') :
    HasAdjoint K
      (fun x => f x - g x)
      (fun y => g' (-y) (f' y)) := by
  constructor
  case adjoint => intro x y; simp [AdjointSpace.inner_sub_left,hf.adjoint,hg.adjoint (-f' y)]; sorry_proof -- missing API
  case is_linear => have := hf.is_linear; have := hg.is_linear; fun_prop
