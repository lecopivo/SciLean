import SciLean.Analysis.AdjointSpace.HasAdjoint
import SciLean.Analysis.Calculus.HasFDeriv
-- import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
-- import SciLean.Tactic.DataSynth.DefRevDeriv


namespace SciLean

variable
  {K : Type*} [RCLike K]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace K X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace K Y]
  {Z : Type*} [NormedAddCommGroup Z] [AdjointSpace K Z]

variable (K)
@[data_synth out f' in f]
structure HasRevFDeriv (f : X → Y) (f' : X → Y×(Y→X)) where
  val : ∀ x, (f' x).1 = f x
  deriv : ∃ df : X → X →L[K] Y,
      (∀ x, HasFDerivAt f (df x) x)
      ∧
      (∀ x, HasAdjoint K (df x) (f' x).2)

@[data_synth out f' in f]
structure HasRevFDerivUpdate (f : X → Y) (f' : X → Y×(Y→X→X)) where
  val : ∀ x, (f' x).1 = f x
  deriv : ∃ df : X → X →L[K] Y,
    (∀ x, HasFDerivAt f (df x) x)
    ∧
    ∃ df' : X → Y →L[K] X,
      (∀ x, HasAdjoint K (df x) (df' x))
      ∧
      (∀ x dy dx, (f' x).2 dy dx = dx + df' x dy)
variable {K}

set_option linter.unusedVariables false in
theorem hasRevFDeriv_from_hasFDerivAt_hasAdjoint {f : X → Y}
    {df : X → X →L[K] Y} (deriv : ∀ x, HasFDerivAt f (df x) x)
    {df' : X → Y → X} (adjoint : ∀ x, HasAdjoint K (df x) (df' x))
    {f'} (simp : f' = (fun x => (f x, df' x))) :
    HasRevFDeriv K f f' := sorry_proof

set_option linter.unusedVariables false in
theorem hasRevFDerivUpdate_from_hasFDerivAt_hasAdjoint {f : X → Y}
    {df : X → X →L[K] Y} (deriv : ∀ x, HasFDerivAt f (df x) x)
    {df' : X → Y → X → X} (adjoint : ∀ x, HasAdjointUpdate K (df x) (df' x))
    {f'} (simp : f' = (fun x => (f x, df' x))) :
    HasRevFDerivUpdate K f f' := sorry_proof


namespace HasRevFDeriv

@[data_synth]
theorem id_rule : HasRevFDeriv K (fun x : X => x) (fun x => (x,fun dy => dy)) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro; simp; data_synth
  case simp => rfl

theorem const_rule : HasRevFDeriv K (fun _ : X => (0 : Y)) (fun _ => 0) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro; eta_expand; simp; data_synth
  case simp => rfl

theorem comp_rule (g : X → Y) (f : Y → Z) {g' f'}
    (hg : HasRevFDeriv K g g') (hf : HasRevFDeriv K f f') :
    HasRevFDeriv K
      (fun x => f (g x))
      (fun x =>
        let' (y,dg') := g' x
        let' (z,df') := f' y
        (z, fun dz =>
          let dy := df' dz
          dg' dy)) := by
  rcases hf with ⟨_,_,_,_⟩
  rcases hg with ⟨_,_,_,_⟩
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro; eta_expand; simp; data_synth
  case simp => simp_all

theorem let_rule (g : X → Y) (f : Y → X → Z) {g' f'}
    (hg : HasRevFDerivUpdate K g g') (hf : HasRevFDeriv K (fun yx : Y×X => f yx.1 yx.2) f') :
    HasRevFDeriv K
      (fun x =>
        let y := g x
        f y x)
      (fun x =>
        let' (y,dg') := g' x
        let' (z,df') := f' (y,x)
        (z, fun dz =>
          let' (dy, dx) := df' dz
          dg' dy dx)) := by
  rcases hf with ⟨_,_,_,_⟩
  rcases hg with ⟨_,_,_,_,_,_⟩
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro; eta_expand; simp; data_synth
  case simp => simp_all; ac_rfl

set_option linter.unusedVariables false in
theorem pi_rule {I : Type*} [IndexType I]
    (f : X → I → Y) {f' : I → _} (hf : ∀ i, HasRevFDerivUpdate K (f · i) (f' i)) :
    HasRevFDeriv K
      (fun x i => f x i)
      (fun x =>
        (fun i => f x i,
         fun dy =>
          IndexType.foldl (init:=(0:X)) fun dx i => (f' i x).2 (dy i) dx)) := by
  sorry_proof

#exit

set_option linter.unusedVariables false in
theorem proj_rule
    {X₁ : Type*} [NormedAddCommGroup X₁] [AdjointSpace K X₁]
    {X₂ : Type*} [NormedAddCommGroup X₂] [AdjointSpace K X₂]
    (f : X → Y) (g : X₁ → Y) /- (eq : X ≃L[K] X₁×X₂) -/ (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) {g'}
    (hg : HasRevFDeriv K g g') (hf : f = fun x => g (p₁ x))
    (hp₁ : IsContinuousLinearMap K p₁) :
    HasRevFDeriv K f
      (fun x =>
        let x₁ := p₁ x
        let' (y,dg') := g' x₁
        (y, fun dy =>
          let dx₁ := dg' dy
          q dx₁ 0)) := by
  rcases hg with ⟨_,dg,hdg,_⟩
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv =>
    intro x
    rw[hf]
    have h := (fun x =>L[K] p₁ x).hasFDerivAt (x:=x); simp at h
    have h' := hdg (p₁ x)
    set_option trace.Meta.Tactic.data_synth true in
    data_synth -- bug :(
  case adjoint => sorry
  case simp => sorry


theorem proj_rule'
    {X₁ : Type*} [NormedAddCommGroup X₁] [AdjointSpace K X₁]
    {X₂ : Type*} [NormedAddCommGroup X₂] [AdjointSpace K X₂]
    (f : X → Y) (g : X₁ → Y) (dec : X ≃L[K] X₁×X₂) {g'}
    (hg : HasRevFDeriv K g g') (hf : f = fun x => g (dec x).1) :
    HasRevFDeriv K f
      (fun x =>
        let x₁ := (dec x).1
        let' (y,dg') := g' x₁
        (y, fun dy =>
          let dx₁ := dg' dy
          dec.symm (dx₁,0))) := by
  rcases hg with ⟨_,_,_,_⟩
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv =>
    intro; rw[hf]
    set_option trace.Meta.Tactic.data_synth true in
    data_synth
  case adjoint => intro; eta_expand; simp; data_synth
  case simp => simp_all; ac_rfl


open Lean Meta
#eval show MetaM Unit from do
   Tactic.DataSynth.addLambdaTheorem (.const ``HasRevFDeriv ``const_rule )
   Tactic.DataSynth.addLambdaTheorem (.comp ``HasRevFDeriv ``comp_rule
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f) (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf))
   Tactic.DataSynth.addLambdaTheorem (.letE ``HasRevFDeriv ``let_rule
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f) (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf))
   Tactic.DataSynth.addLambdaTheorem (.pi ``HasRevFDeriv ``pi_rule (← getConstArgId ``pi_rule `f) (← getConstArgId ``pi_rule `hf))
   Tactic.DataSynth.addLambdaTheorem (.proj ``HasRevFDeriv ``proj_rule
      (← getConstArgId ``proj_rule `f) (← getConstArgId ``proj_rule `g) (← getConstArgId ``proj_rule `p₁) (← getConstArgId ``proj_rule `p₂) (← getConstArgId ``proj_rule `q) (← getConstArgId ``proj_rule `hg))

end HasRevFDeriv

#exit

namespace HasRevFDerivUpdate

@[data_synth]
theorem id_rule : HasRevFDerivUpdate K (fun x : X => x) (fun x x' => x' + x) := by
  constructor
  case adjoint => simp[AdjointSpace.inner_add_right]
  case is_linear => fun_prop

theorem const_rule : HasRevFDerivUpdate K (fun _ : X => (0 : Y)) (fun _ x => x) := by
  constructor
  case adjoint => simp
  case is_linear => fun_prop

theorem comp_rule (g : X → Y) (f : Y → Z) {g' f'}
    (hg : HasRevFDerivUpdate K g g') (hf : HasRevFDeriv K f f') :
    HasRevFDerivUpdate K (fun x => f (g x)) (fun z => g' (f' z)) := by
  constructor
  case adjoint => intro x y; simp [hf.adjoint,hg.adjoint x]
  case is_linear => have := hg.is_linear; have := hf.is_linear; fun_prop

theorem let_rule (g : X → Y) (f : Y → X → Z) {g' f'}
    (hg : HasRevFDerivUpdate K g g') (hf : HasRevFDerivUpdate K (fun yx : Y×X => f yx.1 yx.2) f') :
    HasRevFDerivUpdate K
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
    (f : X → I → Y) {f' : I → _} (hf : ∀ i, HasRevFDerivUpdate K (f · i) (f' i)) :
    HasRevFDerivUpdate K
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
    (hg : HasRevFDerivUpdate K g g') :
    HasRevFDerivUpdate K f
      (fun y x =>
        let x₁ := p₁ x
        let x₂ := p₂ x
        let x₁ := (g' y x₁)
        q x₁ x₂) := sorry_proof

open Lean Meta in
#eval show MetaM Unit from do
   Tactic.DataSynth.addLambdaTheorem (.const ``HasRevFDerivUpdate ``const_rule)
   Tactic.DataSynth.addLambdaTheorem (.comp ``HasRevFDerivUpdate ``comp_rule
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f) (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf))
   Tactic.DataSynth.addLambdaTheorem (.letE ``HasRevFDerivUpdate ``let_rule
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f) (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf))
   Tactic.DataSynth.addLambdaTheorem (.pi ``HasRevFDerivUpdate ``pi_rule (← getConstArgId ``pi_rule `f) (← getConstArgId ``pi_rule `hf))
   Tactic.DataSynth.addLambdaTheorem (.proj ``HasRevFDerivUpdate ``proj_rule
      (← getConstArgId ``proj_rule `f) (← getConstArgId ``proj_rule `g) (← getConstArgId ``proj_rule `p₁) (← getConstArgId ``proj_rule `p₂) (← getConstArgId ``proj_rule `q) (← getConstArgId ``proj_rule `hg))

end HasRevFDerivUpdate

end SciLean
open SciLean

@[data_synth]
theorem Prod.mk.arg_a0a1.HasRevFDeriv_rule (f : X → Y) (g : X → Z)
  (hf : HasRevFDeriv K f f') (hg : HasRevFDerivUpdate K g g') :
  HasRevFDeriv K
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
theorem Prod.mk.arg_a0a1.HasRevFDeriv_rule' (f : X → Y) (g : X → Z)
  (hf : HasRevFDerivUpdate K f f') (hg : HasRevFDeriv K g g') :
  HasRevFDeriv K
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
theorem Prod.mk.arg_a0a1.HasRevFDerivUpdate_rule (f : X → Y) (g : X → Z)
  (hf : HasRevFDerivUpdate K f f') (hg : HasRevFDerivUpdate K g g') :
  HasRevFDerivUpdate K
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
theorem HAdd.hAdd.arg_a0a1.HasRevFDeriv_simple_rule :
    HasRevFDeriv K
      (fun x : X×X => x.1 + x.2)
      (fun x => (x,x)) := by
  constructor
  case adjoint => simp[AdjointSpace.inner_prod_split, AdjointSpace.inner_add_left, AdjointSpace.inner_add_right]
  case is_linear => fun_prop

@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasRevFDerivUpdate_simple_rule :
    HasRevFDerivUpdate K
      (fun x : X×X => x.1 + x.2)
      (fun x x' =>
         let' (x'₁, x'₂) := x'
         (x'₁ + x, x'₂ + x)) := by
  constructor
  case adjoint => simp[AdjointSpace.inner_prod_split, AdjointSpace.inner_add_left, AdjointSpace.inner_add_right]; ring_nf; simp
  case is_linear => fun_prop

@[data_synth]
theorem HSub.hSub.arg_a0a1.HasRevFDeriv_simple_rule :
    HasRevFDeriv K
      (fun x : X×X => x.1 - x.2)
      (fun x => (x, -x)) := by
  constructor
  case adjoint => simp[AdjointSpace.inner_prod_split, AdjointSpace.inner_add_left, AdjointSpace.inner_add_right,sub_eq_add_neg]
  case is_linear => fun_prop

@[data_synth]
theorem HSub.hSub.arg_a0a1.HasRevFDerivUpdate_simple_rule :
    HasRevFDerivUpdate K
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
theorem Neg.neg.arg_a0.HasRevFDeriv_simple_rule :
    HasRevFDeriv K
      (fun x : X => -x)
      (fun x => -x) := by
  constructor
  case adjoint => simp
  case is_linear => fun_prop

@[data_synth]
theorem Neg.neg.arg_a0.HasRevFDerivUpdate_simple_rule :
    HasRevFDerivUpdate K
      (fun x : X => -x)
      (fun x x' => x' - x) := by
  constructor
  case adjoint => simp[AdjointSpace.inner_add_right,sub_eq_add_neg]
  case is_linear => fun_prop

@[data_synth]
theorem HSmul.hSMul.arg_a0.HasRevFDeriv_simp_rule (x : X) :
    HasRevFDeriv K
      (fun k : K => k • x)
      (fun y => ⟪x,y⟫[K]) := by
  constructor
  case adjoint => intro k y; simp [AdjointSpace.inner_smul_left]
  case is_linear => sorry_proof

@[data_synth]
theorem HSmul.hSMul.arg_a0.HasRevFDerivUpdate_simp_rule (x : X) :
    HasRevFDerivUpdate K
      (fun k : K => k • x)
      (fun y k => k + ⟪x,y⟫[K]) := by
  constructor
  case adjoint => intro k y; simp [AdjointSpace.inner_smul_left]; ring_nf; simp
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HSMul.hSMul.arg_a1.HasRevFDeriv_simple_rule (k : K) :
    HasRevFDeriv K
      (fun x : X => k • x)
      (fun x => conj k • x) := by
  constructor
  case adjoint => intro x y; simp [AdjointSpace.inner_smul_left,AdjointSpace.inner_smul_right]
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HSMul.hSMul.arg_a1.HasRevFDerivUpdate_simple_rule (k : K) :
    HasRevFDerivUpdate K
      (fun x : X => k • x)
      (fun x x' => x' + conj k • x) := by
  constructor
  case adjoint =>
    intro x y;
    simp [AdjointSpace.inner_smul_left,AdjointSpace.inner_smul_right,AdjointSpace.inner_add_right]
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HSMul.hSMul.arg_a1.HasRevFDeriv_simple_rule_nat (n : ℕ) :
    HasRevFDeriv K
      (fun x : X => n • x)
      (fun x => n • x) := by
  constructor
  case adjoint => intro x y; sorry_proof
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HSMul.hSMul.arg_a1.HasRevFDerivUpdate_simple_rule_nat (n : ℕ) :
    HasRevFDerivUpdate K
      (fun x : X => n • x)
      (fun x x' => x' + n • x) := by
  constructor
  case adjoint => intro x y; sorry_proof
  case is_linear => sorry_proof

-- todo: finish the proof as I'm not sure if these assumptions are sufficient!!! (but very plausible)
open ComplexConjugate in
@[data_synth]
theorem HSMul.hSMul.arg_a1.HasRevFDeriv_simple_rule_complex_over_real
    {R} [RealScalar R] {K} [RCLike K] [Algebra R K]
    {X} [NormedAddCommGroup X] [AdjointSpace R X] [AdjointSpace K X] [IsScalarTower R K X]
    (k : K) :
    HasRevFDeriv R
      (fun x : X => k • x)
      (fun x => (conj k) • x) := by
  constructor
  case adjoint => intro y z; sorry_proof
  case is_linear => sorry_proof

-- todo: finish the proof as I'm not sure if these assumptions are sufficient!!! (but very plausible)
open ComplexConjugate in
@[data_synth]
theorem HSMul.hSMul.arg_a1.HasRevFDerivUpdate_simple_rule_complex_over_real
    {R} [RealScalar R] {K} [RCLike K] [Algebra R K]
    {X} [NormedAddCommGroup X] [AdjointSpace R X] [AdjointSpace K X] [IsScalarTower R K X]
    (k : K) :
    HasRevFDerivUpdate R
      (fun x : X => k • x)
      (fun x x'=> x' + (conj k) • x) := by
  constructor
  case adjoint => intro y z; sorry_proof
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HMul.hMul.arg_a0.HasRevFDeriv_simp_rule (y : K) :
    HasRevFDeriv K
      (fun x => x * y)
      (fun z => z * conj y) := by
  constructor
  case adjoint => intro k y; simp; ac_rfl
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HMul.hMul.arg_a0.HasRevFDerivUpdate_simp_rule (y : K) :
    HasRevFDerivUpdate K
      (fun x => x * y)
      (fun z x' => x' + z * conj y) := by
  constructor
  case adjoint => intro k y; simp; ring_nf; simp
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HMul.hMul.arg_a1.HasRevFDeriv_simp_rule (x : K) :
    HasRevFDeriv K
      (fun y => x * y)
      (fun z => conj x * z) := by
  constructor
  case adjoint => intro k y; simp; ac_rfl;
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HMul.hMul.arg_a1.HasRevFDerivUpdate_simp_rule (x : K) :
    HasRevFDerivUpdate K
      (fun y => x * y)
      (fun z y' => y' + conj x * z) := by
  constructor
  case adjoint => intro k y; simp; ring_nf; simp
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HDiv.hDiv.arg_a0.HasRevFDeriv_simp_rule (y : K) :
    HasRevFDeriv K
      (fun x => x / y)
      (fun z => z / conj y) := by
  constructor
  case adjoint => intro k y; simp; ring
  case is_linear => sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HDiv.hDiv.arg_a0.HasRevFDerivUpdate_simp_rule (y : K) :
    HasRevFDerivUpdate K
      (fun x => x / y)
      (fun z x' => x' + z / conj y) := by
  constructor
  case adjoint => intro k y; simp; ring_nf; simp
  case is_linear => sorry_proof

@[data_synth]
theorem SciLean.sum.arg_f.HasRevFDeriv_simp_rule {I : Type*} [IndexType I] :
    HasRevFDeriv K
      (fun f : I → X => sum f)
      (fun k _ => k) := by
  constructor
  case adjoint => intro f y; simp[Inner.inner]; sorry_proof -- missing API
  case is_linear => fun_prop

@[data_synth]
theorem SciLean.sum.arg_f.HasRevFDerivUpdate_simp_rule {I : Type*} [IndexType I] :
    HasRevFDerivUpdate K
      (fun f : I → X => sum f)
      (fun k f' i => f' i + k) := by
  constructor
  case adjoint => intro f y; simp[Inner.inner]; sorry_proof -- missing API
  case is_linear => fun_prop

@[data_synth]
theorem Finset.sum.arg_f.HasRevFDeriv_simp_rule {I : Type*} (A : Finset I) [IndexType I] :
    HasRevFDeriv K
      (fun f : I → X => A.sum f)
      (fun k i => A.toSet.indicator (fun _ => k) i) := by
  constructor
  case adjoint => intro f y; simp[Inner.inner]; sorry_proof -- missing API
  case is_linear => fun_prop

@[data_synth]
theorem Finset.sum.arg_f.HasRevFDerivUpdate_simp_rule {I : Type*} (A : Finset I) [IndexType I] :
    HasRevFDerivUpdate K
      (fun f : I → X => A.sum f)
      (fun k f i => f i + A.toSet.indicator (fun _ => k) i) := by
  constructor
  case adjoint => intro f y; simp[Inner.inner]; sorry_proof -- missing API
  case is_linear => fun_prop

@[data_synth]
theorem ite.arg_te.HasRevFDeriv_simple_rule {c : Prop} [Decidable c] :
    HasRevFDeriv K
      (fun te : X×X => if c then te.1 else te.2)
      (fun y => if c then (y,0) else (0,y)) := by
  constructor
  case adjoint => intro x y; split_ifs <;> simp[AdjointSpace.inner_prod_split]
  case is_linear => fun_prop

@[data_synth]
theorem ite.arg_te.HasRevFDerivUpdate_simple_rule {c : Prop} [Decidable c] :
    HasRevFDerivUpdate K
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
theorem Inner.inner.arg_a0.HasRevFDeriv_simple_rule
    {R} [RealScalar R]
    {X} [NormedAddCommGroup X] [AdjointSpace R X]
    (y : X) :
    HasRevFDeriv R
      (fun x : X => ⟪x,y⟫[R])
      (fun k => k•y) := by
  constructor
  case adjoint =>
    intro x k
    simp[AdjointSpace.inner_smul_right,ScalarInner.inner_eq_inner_re_im]
    ac_rfl
  case is_linear => fun_prop

open ComplexConjugate in
@[data_synth]
theorem Inner.inner.arg_a0.HasRevFDerivUpdate_simple_rule
    {R} [RealScalar R]
    {X} [NormedAddCommGroup X] [AdjointSpace R X]
    (y : X) :
    HasRevFDerivUpdate R
      (fun x : X => ⟪x,y⟫[R])
      (fun k x => x + k•y) := by
  constructor
  case adjoint =>
    intro x k
    simp[AdjointSpace.inner_smul_right,ScalarInner.inner_eq_inner_re_im,
         AdjointSpace.inner_add_right]
    intros; ring
  case is_linear => fun_prop

@[data_synth]
theorem Inner.inner.arg_a1.HasRevFDeriv_simple_rule (x : X) :
    HasRevFDeriv K
      (fun y : X => ⟪x,y⟫[K])
      (fun k => k • x) := by
  constructor
  case adjoint => intro y z; simp[AdjointSpace.inner_smul_right]; ac_rfl
  case is_linear => fun_prop

@[data_synth]
theorem Inner.inner.arg_a1.HasRevFDerivUpdate_simple_rule (x : X) :
    HasRevFDerivUpdate K
      (fun y : X => ⟪x,y⟫[K])
      (fun k x' => x' + k • x) := by
  constructor
  case adjoint =>
    intro y z; simp[AdjointSpace.inner_smul_right, AdjointSpace.inner_add_right]
    intros; ring
  case is_linear => fun_prop
