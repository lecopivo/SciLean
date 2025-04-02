import SciLean.Analysis.AdjointSpace.HasAdjoint
import SciLean.Analysis.Calculus.HasFDeriv
import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Data.Nat
-- import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
-- import SciLean.Tactic.DataSynth.DefRevDeriv

import SciLean.Util.RewriteBy

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


----------------------------------------------------------------------------------------------------
-- API for constructing and deconstructing HasRevFDeriv(Update)  -----------------------------------
----------------------------------------------------------------------------------------------------

set_option linter.unusedVariables false in
theorem hasRevFDeriv_from_hasFDerivAt_hasAdjoint {f : X → Y}
    {df : X → X →L[K] Y} (deriv : ∀ x, HasFDerivAt f (df x) x)
    {df' : X → Y → X} (adjoint : ∀ x, HasAdjoint K (df x) (df' x))
    {f'} (simp : f' = (fun x => (f x, df' x))) :
    HasRevFDeriv K f f' := sorry_proof

set_option linter.unusedVariables false in
theorem hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate {f : X → Y}
    {df : X → X →L[K] Y} (deriv : ∀ x, HasFDerivAt f (df x) x)
    {df' : X → Y → X → X} (adjoint : ∀ x, HasAdjointUpdate K (df x) (df' x))
    {f'} (simp : f' = (fun x => (f x, df' x))) :
    HasRevFDerivUpdate K f f' := sorry_proof

theorem hasRevFDeriv_from_hasRevFDeriv {f : X → Y}
    {f'} (deriv : HasRevFDeriv K f f')
    {f''} (simp : f'' = f') :
    HasRevFDeriv K f f'' := by rw[simp]; exact deriv

theorem hasRevFDerivUpdate_from_hasRevFDerivUpdate {f : X → Y}
    {f'} (deriv : HasRevFDerivUpdate K f f')
    {f''} (simp : f'' = f') :
    HasRevFDerivUpdate K f f'' := by rw[simp]; exact deriv

set_option linter.unusedVariables false in
theorem HasRevFDeriv.toHasRevFDerivUpdate {f : X → Y} {f' : X → Y×(Y→X)}
    (h : HasRevFDeriv K f f') :
    HasRevFDerivUpdate K f
      (fun x =>
        let' (y,df') := f' x
        (y, fun dy dx => dx + df' dy)) := sorry_proof

set_option linter.unusedVariables false in
theorem HasRevFDerivUpdate.toHasRevFDeriv {f : X → Y} {f' : X → Y×(Y→X→X)}
    (h : HasRevFDerivUpdate K f f') :
    HasRevFDeriv K f
      (fun x =>
        let' (y,df') := f' x
        (y, fun dy => df' dy 0)) := sorry_proof

set_option linter.unusedVariables false in
def HasRevFDeriv.deriv_adjoint {f : X → Y} {f' : X → Y×(Y→X)}
  (h : HasRevFDeriv K f f') :
  (∀ x, (f' x).1 = f x)
  ∧
  ∃ df : X → X →L[K] Y,
    (∀ x, HasFDerivAt f (df x) x)
    ∧
    (∀ x, HasAdjoint K (df x) ((f' x).2)) := sorry_proof

set_option linter.unusedVariables false in
def HasRevFDerivUpdate.deriv_adjoint {f : X → Y} {f' : X → Y×(Y→X→X)}
  (h : HasRevFDerivUpdate K f f') :
  (∀ x, (f' x).1 = f x)
  ∧
  ∃ df : X → X →L[K] Y,
    (∀ x, HasFDerivAt f (df x) x)
    ∧
    ∃ df' : X → Y → X,
      (∀ x, HasAdjoint K (df x) (df' x))
      ∧
      (∀ x dy dx, (f' x).2 dy dx = dx + df' x dy) := sorry_proof

set_option linter.unusedVariables false in
def HasRevFDerivUpdate.deriv_adjointUpdate {f : X → Y} {f' : X → Y×(Y→X→X)}
  (h : HasRevFDerivUpdate K f f') :
  (∀ x, (f' x).1 = f x)
  ∧
  ∃ df : X → X →L[K] Y,
    (∀ x, HasFDerivAt f (df x) x)
    ∧
    (∀ x, HasAdjointUpdate K (df x) ((f' x).2)) := sorry_proof

set_option linter.unusedVariables false in
-- @[to_data_synth_simproc] -- this attribute should automatically generate the following simproc
theorem revFDeriv_from_hasRevFDeriv
  {f : X → Y} {f'} (hf : HasRevFDeriv K f f') :
  revFDeriv K f = f' := sorry_proof

simproc_decl revFDeriv_simproc (revFDeriv _ _) :=
  mkDataSynthSimproc `revFDeriv_simproc ``revFDeriv_from_hasRevFDeriv


----------------------------------------------------------------------------------------------------
-- Lambda Theorems ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

namespace HasRevFDeriv

@[data_synth]
theorem id_rule : HasRevFDeriv K (fun x : X => x) (fun x => (x,fun dy => dy)) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro; simp; data_synth
  case simp => rfl

theorem const_rule (y : Y) : HasRevFDeriv K (fun _ : X => y) (fun _ => (y, fun _ => 0)) := by
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
          let dx := dg' dy
          dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjoint
  have ⟨_,_,_,_⟩ := hg.deriv_adjoint
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
          let dx := dg' dy dx
          dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjoint
  have ⟨_,_,_,_,_,_⟩ := hg.deriv_adjoint
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro; eta_expand; simp; data_synth
  case simp => simp_all; ac_rfl

@[data_synth]
theorem apply_rule {I} {nI} [IndexType I nI] [Fold I] [DecidableEq I] (i : I) :
    HasRevFDeriv K (fun x : I → X => x i)
      (fun x =>
        (x i, fun dxi j => if i=j then dxi else 0)) := sorry_proof

-- this should not be necessary if once we improve function decomposition in `data_synth` tactic
@[data_synth]
theorem apply_rule' {I} {nI} [IndexType I nI] [Fold I] [DecidableEq I] (i : I) :
    HasRevFDeriv K (fun x : (I → X)×Y => x.1 i)
      (fun x =>
        (x.1 i, fun dxi => (fun j => if i=j then dxi else 0, 0))) := sorry_proof

set_option linter.unusedVariables false in
theorem pi_rule {I : Type*} {nI} [IndexType I nI] [Fold I] [Fold I]
    (f : X → I → Y) {f' : I → _} (hf : ∀ i, HasRevFDerivUpdate K (f · i) (f' i)) :
    HasRevFDeriv K
      (fun x i => f x i)
      (fun x =>
        (fun i => f x i,
         fun dy =>
          IndexType.fold .full (init:=(0:X)) fun i dx =>
            let' (y,df') := f' i x
            let dyi := dy i
            let dx := df' dyi dx
            dx)) := by
  sorry_proof

-- structure Decomposition (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) : Prop where
--   mk_proj : ∀ x, q (p₁ x) (p₂ x) = x
--   proj₁_mk : ∀ x₁ x₂, p₁ (q x₁ x₂) = x₁
--   proj₂_mk : ∀ x₁ x₂, p₂ (q x₁ x₂) = x₂

set_option linter.unusedVariables false in
theorem proj_rule
    {X₁ : Type*} [NormedAddCommGroup X₁] [AdjointSpace K X₁]
    {X₂ : Type*} [NormedAddCommGroup X₂] [AdjointSpace K X₂]
    (f : X → Y) (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) {g'}
    (hg : HasRevFDeriv K g g') (hf : f = fun x => g (p₁ x) := by rfl)
    (hp₁ : IsContinuousLinearMap K p₁ := by fun_prop) /- (hdec : Decomposition p₁ p₂ q) -/ :
    HasRevFDeriv K f
      (fun x =>
        let x₁ := p₁ x
        let' (y,dg') := g' x₁
        (y, fun dy =>
          let dx₁ := dg' dy
          let dx := q dx₁ 0
          dx)) := by
  rcases hg with ⟨_,dg,hdg,_⟩
  sorry_proof
  -- apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  -- case deriv =>
  --   intro x
  --   rw[hf]
  --   have h := (fun x =>L[K] p₁ x).hasFDerivAt (x:=x); simp at h
  --   have h' := hdg (p₁ x)
  --   set_option trace.Meta.Tactic.data_synth true in
  --   data_synth -- bug :(
  -- case adjoint => sorry
  -- case simp => sorry

open Lean Meta
#eval show MetaM Unit from do
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDeriv,``const_rule⟩, .const⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDeriv, ``comp_rule⟩, .comp
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f)
      (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDeriv,``let_rule⟩, .letE
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f)
      (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDeriv,``pi_rule⟩, .pi
      (← getConstArgId ``pi_rule `f) (← getConstArgId ``pi_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDeriv,``proj_rule⟩, .proj
      (← getConstArgId ``proj_rule `f) (← getConstArgId ``proj_rule `g)
      (← getConstArgId ``proj_rule `p₁) (← getConstArgId ``proj_rule `p₂)
      (← getConstArgId ``proj_rule `q) (← getConstArgId ``proj_rule `hg)⟩

end HasRevFDeriv


namespace HasRevFDerivUpdate

@[data_synth]
theorem id_rule : HasRevFDerivUpdate K (fun x : X => x) (fun x => (x, fun dx dx' => dx' + dx)) := by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro; simp; data_synth
  case simp => simp_all

theorem const_rule : HasRevFDerivUpdate K (fun _ : X => (y : Y)) (fun _ => (y, fun _ dx => dx)) := by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro; eta_expand; simp; data_synth
  case simp => simp_all

theorem comp_rule (g : X → Y) (f : Y → Z) {g' f'}
    (hg : HasRevFDerivUpdate K g g') (hf : HasRevFDeriv K f f') :
    HasRevFDerivUpdate K
      (fun x => f (g x))
      (fun x =>
        let' (y,dg') := g' x
        let' (z,df') := f' y
        (z, fun dz dx =>
          let dy := df' dz
          let dx := dg' dy dx
          dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjoint
  have ⟨_,_,_,_⟩ := hg.deriv_adjointUpdate
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro; simp; data_synth
  case simp => simp_all

theorem let_rule (g : X → Y) (f : Y → X → Z) {g' f'}
    (hg : HasRevFDerivUpdate K g g') (hf : HasRevFDerivUpdate K (fun yx : Y×X => f yx.1 yx.2) f') :
    HasRevFDerivUpdate K
      (fun x =>
        let y := g x
        f y x)
      (fun x =>
        let' (y,dg') := g' x
        let' (z,df') := f' (y,x)
        (z, fun dz dx =>
          let' (dy,dx) := df' dz (0,dx)
          let dx := dg' dy dx
          dx)) := by
  have ⟨_,_,_,_,_,_⟩ := hf.deriv_adjoint
  have ⟨_,_,_,hg'⟩ := hg.deriv_adjointUpdate
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro x; simp; data_synth
  case simp =>
    simp_all;
    have h := fun x => (hg' x).apply_eq_zero_add;
    simp +singlePass [h]; ac_rfl

@[data_synth]
theorem apply_rule {I} {nI} [IndexType I nI] [Fold I] [DecidableEq I] (i : I) :
    HasRevFDerivUpdate K (fun x : I → X => x i)
      (fun x =>
        (x i, fun dxi dx j => if i=j then dx j + dxi else dx j)) := sorry_proof

-- this should not be necessary if once we improve function decomposition in `data_synth` tactic
@[data_synth]
theorem apply_rule' {I} {nI} [IndexType I nI] [Fold I] [DecidableEq I] (i : I) :
    HasRevFDerivUpdate K (fun x : (I → X)×Y => x.1 i)
      (fun x =>
        (x.1 i, fun dxi dx => (fun j => if i=j then dx.1 j + dxi else dx.1 j, dx.2))) := sorry_proof

set_option linter.unusedVariables false in
theorem pi_rule {I : Type*} {nI} [IndexType I nI] [Fold I] [Fold I]
    (f : X → I → Y) {f' : I → _} (hf : ∀ i, HasRevFDerivUpdate K (f · i) (f' i)) :
    HasRevFDerivUpdate K
      (fun x i => f x i)
      (fun x =>
        (f x, fun dy dx =>
        IndexType.fold .full (init:=dx) fun i dx =>
          let' (y,df') := f' i x
          let dyi := dy i
          let dx := df' dyi dx
          dx)) := by
  sorry_proof

set_option linter.unusedVariables false in
theorem proj_rule
    {X₁ : Type*} [NormedAddCommGroup X₁] [AdjointSpace K X₁]
    {X₂ : Type*} [NormedAddCommGroup X₂] [AdjointSpace K X₂]
    (f : X → Y) (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) {g'}
    (hg : HasRevFDerivUpdate K g g') (hf : f = fun x => g (p₁ x) := by rfl)
    (hp₁ : IsContinuousLinearMap K p₁ := by fun_prop) :
    HasRevFDerivUpdate K f
      (fun x =>
        let x₁ := p₁ x
        let' (y,dg') := g' x₁
        (y, fun dy dx =>
          let dx₁ := p₁ dx
          let dx₂ := p₂ dx
          let dx₁ := dg' dy dx₁
          let dx := q dx₁ dx₂
          dx)) := sorry_proof

open Lean Meta
#eval show MetaM Unit from do
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDerivUpdate,``const_rule⟩, .const⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDerivUpdate, ``comp_rule⟩, .comp
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f)
      (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDerivUpdate,``let_rule⟩, .letE
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f)
      (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDerivUpdate,``pi_rule⟩, .pi
      (← getConstArgId ``pi_rule `f) (← getConstArgId ``pi_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDerivUpdate,``proj_rule⟩, .proj
      (← getConstArgId ``proj_rule `f) (← getConstArgId ``proj_rule `g)
      (← getConstArgId ``proj_rule `p₁) (← getConstArgId ``proj_rule `p₂)
      (← getConstArgId ``proj_rule `q) (← getConstArgId ``proj_rule `hg)⟩

end HasRevFDerivUpdate

end SciLean
open SciLean

----------------------------------------------------------------------------------------------------
-- Function Theorems  ------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable
  {K : Type*} [RCLike K]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace K X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace K Y]
  {Z : Type*} [NormedAddCommGroup Z] [AdjointSpace K Z]
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace K W]


@[data_synth]
theorem Prod.mk.arg_a0a1.HasRevFDeriv_comp_rule (f : X → Y) (g : X → Z)
  (hf : HasRevFDeriv K f f') (hg : HasRevFDerivUpdate K g g') :
  HasRevFDeriv K
    (fun x => (f x, g x))
    (fun x =>
      let' (y, df') := f' x
      let' (z, dg') := g' x
      ((y,z), fun dyz =>
        let' (dy,dz) := dyz
        let dx := df' dy
        let dx := dg' dz dx
        dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjoint
  have ⟨_,_,_,_⟩ := hg.deriv_adjointUpdate
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro x; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem Prod.mk.arg_a0a1.HasRevFDerivUpdate_comp_rule (f : X → Y) (g : X → Z)
  (hf : HasRevFDerivUpdate K f f') (hg : HasRevFDerivUpdate K g g') :
  HasRevFDerivUpdate K
    (fun x => (f x, g x))
    (fun x =>
      let' (y, df') := f' x
      let' (z, dg') := g' x
      ((y,z), fun dyz dx =>
        let' (dy,dz) := dyz
        let dx := df' dy dx
        let dx := dg' dz dx
        dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjointUpdate
  have ⟨_,_,_,_⟩ := hg.deriv_adjointUpdate
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro x; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem Prod.fst.arg_self.HasREvFDeriv_simple_rule :
    HasRevFDeriv K (fun xy : X×Y => xy.1) (fun xy => (xy.1, fun dx => (dx,0))) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro x; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem Prod.fst.arg_self.HasREvFDerivUpdate_simple_rule :
    HasRevFDerivUpdate K
      (fun xy : X×Y => xy.1)
      (fun xy => (xy.1, fun dx dxy => let' (dx',dy') := dxy; (dx'+dx,dy'))) := by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro x; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem Prod.snd.arg_self.HasREvFDeriv_simple_rule :
    HasRevFDeriv K (fun xy : X×Y => xy.2) (fun xy => (xy.2, fun dy => (0,dy))) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro x; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem Prod.snd.arg_self.HasREvFDerivUpdate_simple_rule :
    HasRevFDerivUpdate K
      (fun xy : X×Y => xy.2)
      (fun xy => (xy.2, fun dy dxy => let' (dx',dy') := dxy; (dx',dy'+dy))) := by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro x; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasRevFDeriv_rule
    (f g : X → Y) (f' g')
    (hf : HasRevFDeriv K f f') (hg : HasRevFDerivUpdate K g g') :
    HasRevFDeriv K (fun x => f x + g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y + z, fun dy =>
                  let dx := df dy
                  let dx := dg dy dx
                  dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjoint
  have ⟨_,_,_,_⟩ := hg.deriv_adjointUpdate
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro x; eta_expand; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasRevFDerivUpdate_rule
    (f g : X → Y) (f' g')
    (hf : HasRevFDerivUpdate K f f') (hg : HasRevFDerivUpdate K g g') :
    HasRevFDerivUpdate K (fun x => f x + g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y + z, fun dy dx =>
                  let dx := df dy dx
                  let dx := dg dy dx
                  dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjointUpdate
  have ⟨_,_,_,_⟩ := hg.deriv_adjointUpdate
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro x; eta_expand; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem HSub.hSub.arg_a0a1.HasRevFDeriv_rule
    (f g : X → Y) (f' g')
    (hf : HasRevFDeriv K f f') (hg : HasRevFDerivUpdate K g g') :
    HasRevFDeriv K (fun x => f x - g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y - z, fun dy =>
                  let dx := df dy
                  let dx := dg (-dy) dx
                  dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjoint
  have ⟨_,_,_,_⟩ := hg.deriv_adjointUpdate
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro x; eta_expand; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem HSub.hSub.arg_a0a1.HasRevFDerivUpdate_rule
    (f g : X → Y) (f' g')
    (hf : HasRevFDerivUpdate K f f') (hg : HasRevFDerivUpdate K g g') :
    HasRevFDerivUpdate K (fun x => f x - g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y - z, fun dy dx =>
                  let dx := df dy dx
                  let dx := dg (-dy) dx
                  dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjointUpdate
  have ⟨_,_,_,_⟩ := hg.deriv_adjointUpdate
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro x; eta_expand; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem Neg.neg.arg_a0.HasRevFDeriv_rule
    (f : X → Y) (f')
    (hf : HasRevFDeriv K f f') :
    HasRevFDeriv K (fun x => -f x)
      (fun x =>
        let' (y,df) := f' x
        (-y, fun dy =>
          let dx := df (-dy)
          dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjoint
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro x; eta_expand; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem Neg.neg.arg_a0.HasRevFDerivUpdate_rule
    (f : X → Y) (f')
    (hf : HasRevFDerivUpdate K f f') :
    HasRevFDerivUpdate K (fun x => -f x)
      (fun x =>
        let' (y,df) := f' x
        (-y, fun dy dx =>
          let dx := df (-dy) dx
          dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjointUpdate
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro x; eta_expand; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem Neg.neg.arg_a0.HasRevFDeriv_simple_rule :
    HasRevFDeriv K (fun x : X => -x)
      (fun x =>
        let x := -x
        (x, fun dy => let dy := -dy; dy)) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro x; eta_expand; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem Neg.neg.arg_a0.HasRevFDerivUpdate_simple_rule :
    HasRevFDerivUpdate K (fun x : X => -x)
      (fun x =>
        let x := -x
        (x, fun dy dx => let dx := dx - dy; dx)) := by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro x; eta_expand; simp; data_synth
  case simp => simp_all

open ComplexConjugate in
@[data_synth]
theorem HSMul.hSMul.arg_a0a1.HasRevFDeriv_rule
    (f : X → K) (g : X → Y) (f' g')
    (hf : HasRevFDerivUpdate K f f') (hg : HasRevFDeriv K g g') :
    HasRevFDeriv K (fun x => f x • g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y • z, fun dy : Y =>
          let ds := ⟪z, dy⟫[K]
          let dx := dg (conj y•dy)
          let dx := df ds dx
          dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjointUpdate
  have ⟨_,_,_,_⟩ := hg.deriv_adjoint
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro x; eta_expand; simp; data_synth
  case simp => simp_all

open ComplexConjugate in
@[data_synth]
theorem HSMul.hSMul.arg_a0a1.HasRevFDerivUpdate_rule
    (f : X → K) (g : X → Y) (f' g')
    (hf : HasRevFDerivUpdate K f f') (hg : HasRevFDerivUpdate K g g') :
    HasRevFDerivUpdate K (fun x => f x • g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y • z, fun dy dx =>
          let ds := ⟪z, dy⟫[K]
          let dx := dg (conj y•dy) dx
          let dx := df ds dx
          dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjointUpdate
  have ⟨_,_,_,_⟩ := hg.deriv_adjointUpdate
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro x; eta_expand; simp; data_synth
  case simp => simp_all

open ComplexConjugate in
@[data_synth]
theorem HMul.hMul.arg_a0a1.HasRevFDeriv_rule
    (f g : X → K) (f' g')
    (hf : HasRevFDerivUpdate K f f') (hg : HasRevFDeriv K g g') :
    HasRevFDeriv K (fun x => f x * g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y * z, fun dy =>
          let dy₁ := (conj y) • dy
          let dy₂ := (conj z) • dy
          let dx := dg dy₁
          let dx := df dy₂ dx
          dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjointUpdate
  have ⟨_,_,_,_⟩ := hg.deriv_adjoint
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro x; eta_expand; simp; data_synth
  case simp => simp_all; sorry_proof -- push smul

open ComplexConjugate in
@[data_synth]
theorem HMul.hMul.arg_a0a1.HasRevFDerivUpdate_rule
    (f g : X → K) (f' g')
    (hf : HasRevFDerivUpdate K f f') (hg : HasRevFDerivUpdate K g g') :
    HasRevFDerivUpdate K (fun x => f x * g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y * z, fun dy dx =>
          let dy₁ := (conj y) • dy
          let dy₂ := (conj z) • dy
          let dx := dg dy₁ dx
          let dx := df dy₂ dx
          dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjointUpdate
  have ⟨_,_,_,_⟩ := hg.deriv_adjointUpdate
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro x; eta_expand; simp; data_synth
  case simp => simp_all

-- TODO: !!!check this!!!
set_option linter.unusedVariables false in
open ComplexConjugate in
@[data_synth]
theorem HDiv.hDiv.arg_a0a1.HasRevFDeriv_rule
    (f g : X → K) (f' g')
    (hf : HasRevFDerivUpdate K f f') (hg : HasRevFDeriv K g g') (hg' : ∀ x, g x ≠ 0) :
    HasRevFDeriv K (fun x => f x / g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y / z, fun dy =>
          let s := ((conj z)^2)⁻¹
          let dy₁ := -s * (conj y) • dy
          let dy₂ := s * (conj z) • dy
          let dx := dg dy₁
          let dx := df dy₂ dx
          dx)) := by
  sorry_proof
  -- have ⟨_,_,_,_⟩ := hf.deriv_adjointUpdate
  -- have ⟨_,_,_,_⟩ := hg.deriv_adjoint
  -- apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  -- case deriv =>
  --   set_option trace.Meta.Tactic.data_synth true in
  --   intro; data_synth
  -- case adjoint => intro x; eta_expand; simp; data_synth
  -- case simp => simp_all

open ComplexConjugate in
set_option linter.unusedVariables false in
@[data_synth]
theorem HDiv.hDiv.arg_a0a1.HasRevFDerivUpdate_rule
    (f g : X → K) (f' g')
    (hf : HasRevFDerivUpdate K f f') (hg : HasRevFDerivUpdate K g g') (hg' : ∀ x, g x ≠ 0) :
    HasRevFDerivUpdate K (fun x => f x / g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y / z, fun dy dx =>
          let s := ((conj z)^2)⁻¹
          let dy₁ := -s * (conj y) • dy
          let dy₂ := s * (conj z) • dy
          let dx := dg dy₁ dx
          let dx := df dy₂ dx
          dx)) := by
  sorry_proof
  -- have ⟨_,_,_,_⟩ := hf.deriv_adjointUpdate
  -- have ⟨_,_,_,_⟩ := hg.deriv_adjoint
  -- apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  -- case deriv =>
  --   set_option trace.Meta.Tactic.data_synth true in
  --   intro; data_synth
  -- case adjoint => intro x; eta_expand; simp; data_synth
  -- case simp => simp_all

open ComplexConjugate in
set_option linter.unusedVariables false in
@[data_synth]
theorem HInv.hInv.arg_a0.HasRevFDeriv_rule
    (f : X → K) (f')
    (hf : HasRevFDeriv K f f') (hf' : ∀ x, f x ≠ 0) :
    HasRevFDeriv K (fun x => (f x)⁻¹)
      (fun x =>
        let' (y,df) := f' x
        (y⁻¹, fun dy =>
          let s := ((conj y)^2)⁻¹
          let dy₁ := -s • dy
          let dx := df dy₁
          dx)) := by
  sorry_proof
  -- have ⟨_,_,_,_⟩ := hf.deriv_adjoint
  -- apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  -- case deriv => intro; data_synth
  -- case adjoint => intro x; eta_expand; simp; data_synth
  -- case simp => simp_all

open ComplexConjugate in
set_option linter.unusedVariables false in
@[data_synth]
theorem HInv.hInv.arg_a0.HasRevFDerivUpdate_rule
    (f : X → K) (f')
    (hf : HasRevFDerivUpdate K f f') (hf' : ∀ x, f x ≠ 0) :
    HasRevFDerivUpdate K (fun x => (f x)⁻¹)
      (fun x =>
        let' (y,df) := f' x
        (y⁻¹, fun dy dx =>
          let s := ((conj y)^2)⁻¹
          let dy₁ := -s • dy
          let dx := df dy₁ dx
          dx)) := by
  sorry_proof
  -- have ⟨_,_,_,_⟩ := hf.deriv_adjointUpdate
  -- apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  -- case deriv => intro; data_synth
  -- case adjoint => intro x; eta_expand; simp; data_synth
  -- case simp => simp_all

open ComplexConjugate in
@[data_synth]
theorem HPow.hPow.arg_a0.HasRevFDeriv_rule
    (f : X → K) (n : ℕ) (f')
    (hf : HasRevFDeriv K f f') :
    HasRevFDeriv K (fun x => f x ^ n)
      (fun x =>
        let' (y,df) := f' x
        (y ^ n, fun dy =>
          let dx := df (n * (conj y)^(n-1) • dy)
          dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjoint
  sorry_proof
  -- apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  -- case deriv => intro; data_synth
  -- case adjoint =>
  --   intro x; eta_expand at *; simp_all;
  --   set_option trace.Meta.Tactic.data_synth true in
  --   data_synth
  -- case simp => simp_all

set_option linter.unusedVariables false in
open ComplexConjugate in
@[data_synth]
theorem HPow.hPow.arg_a0.HasRevFDerivUpdate_rule
    (f : X → K) (n : ℕ) (f')
    (hf : HasRevFDerivUpdate K f f') :
    HasRevFDerivUpdate K (fun x => f x ^ n)
      (fun x =>
        let' (y,df) := f' x
        (y ^ n, fun dy dx =>
          let dx := df (n * (conj y)^(n-1) • dy) dx
          dx)) := by
  sorry_proof

@[data_synth]
theorem SciLean.sum.arg_f.HasRevFDeriv_rule
    {I : Type*} {nI} [IndexType I nI]  [Fold I]  [Fold I] :
    HasRevFDeriv K
      (fun f : I → X => ∑ᴵ i, f i)
      (fun f =>
        (∑ᴵ i, f i, fun dx _ => dx)) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro x; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem SciLean.sum.arg_f.HasRevFDeriv_rule'
    {I : Type*} {nI} [IndexType I nI]  [Fold I] [Fold I] :
    HasRevFDeriv K
      (fun f : I → X => IndexType.sum f)
      (fun f =>
        (∑ᴵ i, f i, fun dx _ => dx)) := by
  apply SciLean.sum.arg_f.HasRevFDeriv_rule

@[data_synth]
theorem SciLean.sum.arg_f.HasRevFDerivUpdate_rule
    {I : Type*} {nI} [IndexType I nI] [Fold I] [Fold I] :
    HasRevFDerivUpdate K
      (fun f : I → X => ∑ᴵ i, f i)
      (fun f =>
        (∑ᴵ i, f i, fun dx df i =>
          let dxi := df i
          let dx := dxi + dx
          dx)) := by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro x; simp; data_synth
  case simp => simp_all

-- we have to formulate it this way too because some issue with RefinedDiscrTree
-- once mathlib PR #11968 is merges this should not be necessaryx
@[data_synth]
theorem SciLean.sum.arg_f.HasRevFDerivUpdate_rule'
    {I : Type*} {nI} [IndexType I nI] [Fold I] [Fold I] :
    HasRevFDerivUpdate K
      (fun f : I → X => IndexType.sum f)
      (fun f =>
        (∑ᴵ i, f i, fun dx df i =>
          let dxi := df i
          let dx := dxi + dx
          dx)) := by
  apply SciLean.sum.arg_f.HasRevFDerivUpdate_rule

@[data_synth]
theorem Finset.sum.arg_f.HasRevFDeriv_rule
    {I : Type*} {nI} [IndexType I nI] [Fold I] (A : Finset I) :
    HasRevFDeriv K
      (fun f : I → X => A.sum (fun i => f i))
      (fun f =>
        (A.sum (fun i => f i), fun dx i => A.toSet.indicator (fun _ => dx) i)) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro x; simp; data_synth
  case simp => rfl

-- we have to formulate it this way too because some issue with RefinedDiscrTree
-- once mathlib PR #11968 is merges this should not be necessaryx
@[data_synth]
theorem Finset.sum.arg_f.HasRevFDeriv_rule'
    {I : Type*} {nI} [IndexType I nI] [Fold I] (A : Finset I) :
    HasRevFDeriv K
      (fun f : I → X => A.sum f)
      (fun f =>
        (A.sum (fun i => f i), fun dx i => A.toSet.indicator (fun _ => dx) i)) := by
  apply Finset.sum.arg_f.HasRevFDeriv_rule

@[data_synth]
theorem Finset.sum.arg_f.HasRevFDerivUpdate_rule
    {I : Type*} {nI} [IndexType I nI] [Fold I] (A : Finset I) :
    HasRevFDerivUpdate K
      (fun f : I → X => A.sum (fun i => f i))
      (fun f =>
        (A.sum (fun i => f i), fun dx df i => df i + A.toSet.indicator (fun _ => dx) i)) := by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro x; simp; data_synth
  case simp => rfl

-- we have to formulate it this way too because some issue with RefinedDiscrTree
-- once mathlib PR #11968 is merges this should not be necessaryx
@[data_synth]
theorem Finset.sum.arg_f.HasRevFDerivUpdate_rule'
    {I : Type*} {nI} [IndexType I nI] [Fold I] (A : Finset I) :
    HasRevFDerivUpdate K
      (fun f : I → X => A.sum (f))
      (fun f =>
        (A.sum (fun i => f i), fun dx df i =>
          let dxi := df i
          let dx := dxi + A.toSet.indicator (fun _ => dx) i
          dx)) := by
  apply Finset.sum.arg_f.HasRevFDerivUpdate_rule

@[data_synth]
theorem ite.arg_te.HasRevFDeriv_rule (c : Prop) (dec : Decidable c)
    (f g : W → X) (f' g') (hf : HasRevFDeriv K f f') (hg : HasRevFDeriv K g g') :
    HasRevFDeriv K
      (fun w => if c then f w else g w)
      (fun w => if c then f' w else g' w) := by
  split_ifs <;> assumption

@[data_synth]
theorem ite.arg_te.HasRevFDerivUpdate_rule (c : Prop) (dec : Decidable c)
    (f g : W → X) (f' g') (hf : HasRevFDerivUpdate K f f') (hg : HasRevFDerivUpdate K g g') :
    HasRevFDerivUpdate K
      (fun w => if c then f w else g w)
      (fun w => if c then f' w else g' w) := by
  split_ifs <;> assumption

@[data_synth]
theorem dite.arg_te.HasRevFDeriv_rule (c : Prop) (dec : Decidable c)
    (f : c → W → X) (g : ¬c → W → X) (f' : c → _) (g' : ¬c → _)
    (hf : ∀ h, HasRevFDeriv K (f h) (f' h)) (hg : ∀ h, HasRevFDeriv K (g h) (g' h)) :
    HasRevFDeriv K
      (fun w => if h : c then f h w else g h w)
      (fun w => if h : c then f' h w else g' h w) := by
  by_cases h : c
  · simp [h]; apply (hf h)
  · simp [h]; apply (hg h)

@[data_synth]
theorem dite.arg_te.HasRevFDerivUpdate_rule (c : Prop) (dec : Decidable c)
    (f : c → W → X) (g : ¬c → W → X) (f' : c → _) (g' : ¬c → _)
    (hf : ∀ h, HasRevFDerivUpdate K (f h) (f' h)) (hg : ∀ h, HasRevFDerivUpdate K (g h) (g' h)) :
    HasRevFDerivUpdate K
      (fun w => if h : c then f h w else g h w)
      (fun w => if h : c then f' h w else g' h w) := by
  by_cases h : c
  · simp [h]; apply (hf h)
  · simp [h]; apply (hg h)


section OverReals

variable {R K : Type*} [RealScalar R] [Scalar R K] [ScalarSMul R K] [ScalarInner R K]
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace R Y] [AdjointSpace K Y]

open ComplexConjugate

@[data_synth]
theorem Inner.inner.arg_a0a1.HasRevFDeriv_comp_rule
  (f g : X → Y) (f' g')
  (hf : HasRevFDeriv R f f') (hg : HasRevFDerivUpdate R g g') :
  HasRevFDeriv R
    (fun x => ⟪f x, g x⟫[K])
    (fun x =>
      let' (y,df) := f' x
      let' (z,dg) := g' x
      (⟪y,z⟫[K], fun dr =>
        let dx := df (conj dr • z)
        let dx := dg (dr • y) dx
        dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjoint
  have ⟨_,_,_,_⟩ := hg.deriv_adjointUpdate
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro x; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem Inner.inner.arg_a0a1.HasRevFDerivUpdate_comp_rule
  (f g : X → Y) (f' g')
  (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
  HasRevFDerivUpdate R
    (fun x => ⟪f x, g x⟫[K])
    (fun x =>
      let' (y,df) := f' x
      let' (z,dg) := g' x
      (⟪y,z⟫[K], fun dr dx =>
        let dx := df (conj dr • z) dx
        let dx := dg (dr • y) dx
        dx)) := by
  have ⟨_,_,_,_⟩ := hf.deriv_adjointUpdate
  have ⟨_,_,_,_⟩ := hg.deriv_adjointUpdate
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro x; simp; data_synth
  case simp => simp_all

@[data_synth]
theorem Norm2.norm2.arg_a0.HasRevFDeriv_simple_rule :
  HasRevFDeriv R
    (fun x : X => ‖x‖₂²[R])
    (fun x =>
      let s := ‖x‖₂²[R];
      (s, fun dr =>
        let dx := (2*dr) • x
        dx)) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro; dsimp; data_synth
  case simp => funext x; simp; funext dr; module

@[data_synth]
theorem Norm2.norm2.arg_a0.HasRevFDerivUpdate_simple_rule :
  HasRevFDerivUpdate R
    (fun x : X => ‖x‖₂²[R])
    (fun x =>
      let s := ‖x‖₂²[R];
      (s, fun dr x' =>
        let dx := (2*dr) • x + x'
        dx)) := by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro; dsimp; data_synth
  case simp => funext x; simp; funext dr x'; module

set_option linter.unusedVariables false in
@[data_synth]
theorem norm2.arg_a0.HasRevFDeriv_rule
    (f : X → Y) (f')
    (hf : HasRevFDeriv R f f') (hf' : ∀ x, f x ≠ 0) :
    HasRevFDeriv R (fun x => ‖f x‖₂[R])
      (fun x =>
        let' (y,df) := f' x
        let ynorm := ‖y‖₂[R]
        (ynorm, fun dr =>
          let dy := (dr * ynorm⁻¹) • y
          let dx := df dy
          dx)) := by
  sorry_proof

set_option linter.unusedVariables false in
@[data_synth]
theorem norm2.arg_a0.HasRevFDerivUpdate_rule
    (f : X → Y) (f')
    (hf : HasRevFDerivUpdate R f f') (hf' : ∀ x, f x ≠ 0) :
    HasRevFDerivUpdate R (fun x => ‖f x‖₂[R])
      (fun x =>
        let' (y,df) := f' x
        let ynorm := ‖y‖₂[R]
        (ynorm, fun dr dx =>
          let dy := (dr * ynorm⁻¹) • y
          let dx := df dy dx
          dx)) := by
  sorry_proof

end OverReals


----------------------------------------------------------------------------------------------------
-- Recursion theorems ------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


theorem hasRevFDeriv_nat_induction
    {X : ℕ → Type*} [∀ n, NormedAddCommGroup (X n)] [∀ n, AdjointSpace K (X n)]
    {Y : ℕ → Type*} [∀ n, NormedAddCommGroup (Y n)] [∀ n, AdjointSpace K (Y n)]
    (n) (f : (n : ℕ) → X n → Y n)
    {f₀' : X 0 → Y 0 × (Y 0 → X 0)}
    {F' : {m : ℕ} → (X m →  Y m × (Y m → X m)) → X (m+1) → Y (m+1) × (Y (m+1) → X (m+1))}
    (zero : HasRevFDeriv K (f 0) (fun x => f₀' x))
    (succ : ∀ n (fn' : X n → Y n × (Y n → X n)),
             (HasRevFDeriv K (f n) fn')
             →
             HasRevFDeriv K (f (n+1)) (fun x => F' fn' x)) :
    HasRevFDeriv K (f n) (fun x => natRecFun (n:=n) (X:=fun n => X n) F' f₀' x) := by
  induction n
  case zero => exact zero
  case succ n hn => exact succ n _ hn


theorem hasRevFDerivUpdate_nat_induction
    {X : ℕ → Type*} [∀ n, NormedAddCommGroup (X n)] [∀ n, AdjointSpace K (X n)]
    {Y : ℕ → Type*} [∀ n, NormedAddCommGroup (Y n)] [∀ n, AdjointSpace K (Y n)]
    (n) (f : (n : ℕ) → X n → Y n)
    {f₀' : X 0 → Y 0 × (Y 0 → X 0 → X 0)}
    {F' : {m : ℕ} → (X m →  Y m × (Y m → X m → X m)) → X (m+1) → Y (m+1) × (Y (m+1) → X (m+1) → X (m+1))}
    (zero : HasRevFDerivUpdate K (f 0) (fun x => f₀' x))
    (succ : ∀ n (fn' : X n → Y n × (Y n → X n → X n)),
             (HasRevFDerivUpdate K (f n) fn')
             →
             HasRevFDerivUpdate K (f (n+1)) (fun x => F' fn' x)) :
    HasRevFDerivUpdate K (f n) (fun x => natRecFun (n:=n) (X:=fun n => X n) F' f₀' x) := by
  induction n
  case zero => exact zero
  case succ n hn => exact succ n _ hn
