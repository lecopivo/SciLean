module

public import SciLean.Analysis.AdjointSpace.HasAdjoint
public import SciLean.Analysis.Calculus.HasFDeriv
public import SciLean.Analysis.Calculus.RevFDeriv
public import SciLean.Analysis.SpecialFunctions.Norm2
public import SciLean.Data.Nat
-- import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
-- import SciLean.Tactic.DataSynth.DefRevDeriv

public import SciLean.Util.RewriteBy

@[expose] public section


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

theorem hasRevFDeriv_from_hasFDerivAt_hasAdjoint {f : X → Y}
    {df : X → X →L[K] Y} (deriv : ∀ x, HasFDerivAt f (df x) x)
    {df' : X → Y → X} (adjoint : ∀ x, HasAdjoint K (df x) (df' x))
    {f'} (simp : f' = (fun x => (f x, df' x))) :
    HasRevFDeriv K f f' where
  val := by subst simp; intro x; rfl
  deriv := ⟨df, deriv, by subst simp; exact adjoint⟩

theorem hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate {f : X → Y}
    {df : X → X →L[K] Y} (deriv : ∀ x, HasFDerivAt f (df x) x)
    {df' : X → Y → X → X} (adjoint : ∀ x, HasAdjointUpdate K (df x) (df' x))
    {f'} (simp : f' = (fun x => (f x, df' x))) :
    HasRevFDerivUpdate K f f' := by
  subst simp
  refine ⟨fun x => rfl, df, deriv,
    fun x => ContinuousLinearMap.mk' K (fun dy => df' x dy 0)
      ((adjoint x).hasAdjoint.isContinuousLinearMap'), fun x => (adjoint x).hasAdjoint, ?_⟩
  intro x dy dx
  show df' x dy dx = dx + df' x dy 0
  rw [(adjoint x).apply_eq_zero_add dx dy, add_comm]

theorem hasRevFDeriv_from_hasRevFDeriv {f : X → Y}
    {f'} (deriv : HasRevFDeriv K f f')
    {f''} (simp : f'' = f') :
    HasRevFDeriv K f f'' := by rw[simp]; exact deriv

theorem hasRevFDerivUpdate_from_hasRevFDerivUpdate {f : X → Y}
    {f'} (deriv : HasRevFDerivUpdate K f f')
    {f''} (simp : f'' = f') :
    HasRevFDerivUpdate K f f'' := by rw[simp]; exact deriv

theorem HasRevFDeriv.toHasRevFDerivUpdate {f : X → Y} {f' : X → Y×(Y→X)}
    (h : HasRevFDeriv K f f') :
    HasRevFDerivUpdate K f
      (fun x =>
        let' (y,df') := f' x
        (y, fun dy dx => dx + df' dy)) := by
  obtain ⟨val, df, hd, ha⟩ := h
  refine ⟨val, df, hd, fun x => ContinuousLinearMap.mk' K ((f' x).2) (ha x).isContinuousLinearMap',
    fun x => ha x, ?_⟩
  intros; rfl

theorem HasRevFDerivUpdate.toHasRevFDeriv {f : X → Y} {f' : X → Y×(Y→X→X)}
    (h : HasRevFDerivUpdate K f f') :
    HasRevFDeriv K f
      (fun x =>
        let' (y,df') := f' x
        (y, fun dy => df' dy 0)) := by
  obtain ⟨val, df, hd, dfc, ha, hupd⟩ := h
  refine ⟨val, df, hd, fun x => ?_⟩
  show HasAdjoint K (⇑(df x)) (fun dy => (f' x).2 dy 0)
  rw [show ((fun dy => (f' x).2 dy 0) : Y → X) = ⇑(dfc x) from
    funext fun dy => by rw [hupd x dy 0, zero_add]]
  exact ha x

theorem HasRevFDerivUpdate.apply_eq_zero_add {f : X → Y} {f' : X → Y×(Y→X→X)}
    (h : HasRevFDerivUpdate K f f') (x : X) (dy : Y) (dx : X) :
    (f' x).2 dy dx = dx + (f' x).2 dy 0 := by
  obtain ⟨df, hd, df', ha, hupd⟩ := h.deriv
  rw [hupd x dy dx, hupd x dy 0, zero_add]

theorem HasRevFDeriv.deriv_adjoint {f : X → Y} {f' : X → Y×(Y→X)}
  (h : HasRevFDeriv K f f') :
  (∀ x, (f' x).1 = f x)
  ∧
  ∃ df : X → X →L[K] Y,
    (∀ x, HasFDerivAt f (df x) x)
    ∧
    (∀ x, HasAdjoint K (df x) ((f' x).2)) := ⟨h.val, h.deriv⟩

theorem HasRevFDerivUpdate.deriv_adjoint {f : X → Y} {f' : X → Y×(Y→X→X)}
  (h : HasRevFDerivUpdate K f f') :
  (∀ x, (f' x).1 = f x)
  ∧
  ∃ df : X → X →L[K] Y,
    (∀ x, HasFDerivAt f (df x) x)
    ∧
    ∃ df' : X → Y → X,
      (∀ x, HasAdjoint K (df x) (df' x))
      ∧
      (∀ x dy dx, (f' x).2 dy dx = dx + df' x dy) := by
  obtain ⟨df, hd, df', ha, hupd⟩ := h.deriv
  exact ⟨h.val, df, hd, fun x => (df' x : Y → X), ha, hupd⟩

theorem HasRevFDerivUpdate.deriv_adjointUpdate {f : X → Y} {f' : X → Y×(Y→X→X)}
  (h : HasRevFDerivUpdate K f f') :
  (∀ x, (f' x).1 = f x)
  ∧
  ∃ df : X → X →L[K] Y,
    (∀ x, HasFDerivAt f (df x) x)
    ∧
    (∀ x, HasAdjointUpdate K (df x) ((f' x).2)) := by
  obtain ⟨df, hd, df', ha, hupd⟩ := h.deriv
  exact ⟨h.val, df, hd,
         fun x => hasAdjointUpdate_from_hasAdjoint (ha x) (fun dy dx => hupd x dy dx)⟩

-- @[to_data_synth_simproc] -- this attribute should automatically generate the following simproc
theorem revFDeriv_from_hasRevFDeriv
  {f : X → Y} {f'} (hf : HasRevFDeriv K f f') :
  revFDeriv K f = f' := by
  obtain ⟨val, df, hd, ha⟩ := hf
  funext x
  rw [revFDeriv]
  refine Prod.ext (val x).symm ?_
  simp only [(hd x).fderiv]
  exact adjoint_from_hasAdjoint (ha x)

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

/-- The adjoint of the evaluation map `x ↦ x i` is `dxi ↦ fun j => if i = j then dxi else 0`. -/
theorem hasAdjoint_apply {I} {nI} [IndexType I nI] [Fold I] [DecidableEq I] (i : I) :
    HasAdjoint K (fun x : I → X => x i) (fun dxi j => if i=j then dxi else 0) := by
  constructor
  case adjoint =>
    intro x y
    rw [show (⟪x, fun j => if i = j then y else 0⟫[K])
          = ∑ᴵ j, ⟪x j, (if i = j then y else 0 : X)⟫[K] from rfl,
      SciLean.IndexType.sum_eq_finset_sum, Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  case is_linear => fun_prop

/-- The adjoint of `x ↦ x.1 i` on a product. -/
theorem hasAdjoint_apply' {I} {nI} [IndexType I nI] [Fold I] [DecidableEq I] (i : I) :
    HasAdjoint K (fun x : (I → X)×Y => x.1 i)
      (fun dxi => ((fun j => if i=j then dxi else 0 : I → X), (0:Y))) := by
  constructor
  case adjoint =>
    intro u y
    show ⟪u.1 i, y⟫[K] = ⟪u, ((fun j => if i = j then y else 0 : I → X), (0:Y))⟫[K]
    rw [AdjointSpace.inner_prod_split, (hasAdjoint_apply (X:=X) i).adjoint u.1 y]
    simp
  case is_linear => fun_prop

@[data_synth]
theorem apply_rule {I} {nI} [IndexType I nI] [Fold I] [DecidableEq I] (i : I) :
    HasRevFDeriv K (fun x : I → X => x i)
      (fun x =>
        (x i, fun dxi j => if i=j then dxi else 0)) := by
  have hclm : IsContinuousLinearMap K (fun x : I → X => x i) := by fun_prop
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (df := fun _ => ContinuousLinearMap.mk' K (fun x : I → X => x i) hclm)
  case deriv => intro x; exact (ContinuousLinearMap.mk' K (fun x : I → X => x i) hclm).hasFDerivAt
  case adjoint => intro x; exact hasAdjoint_apply i
  case simp => rfl

-- this should not be necessary if once we improve function decomposition in `data_synth` tactic
@[data_synth]
theorem apply_rule' {I} {nI} [IndexType I nI] [Fold I] [DecidableEq I] (i : I) :
    HasRevFDeriv K (fun x : (I → X)×Y => x.1 i)
      (fun x =>
        (x.1 i, fun dxi => (fun j => if i=j then dxi else 0, 0))) := by
  have hclm : IsContinuousLinearMap K (fun x : (I → X)×Y => x.1 i) := by fun_prop
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (df := fun _ => ContinuousLinearMap.mk' K (fun x : (I → X)×Y => x.1 i) hclm)
  case deriv => intro x; exact (ContinuousLinearMap.mk' K (fun x : (I → X)×Y => x.1 i) hclm).hasFDerivAt
  case adjoint => intro x; exact hasAdjoint_apply' i
  case simp => rfl

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
  choose df hdf df' hadj hupd using fun i => (hf i).deriv
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (df := fun x => ContinuousLinearMap.pi (fun i => df i x))
    (df' := fun x dy => IndexType.fold .full (init:=(0:X)) fun i dx => (f' i x).2 (dy i) dx)
  case deriv =>
    intro x
    rw [hasFDerivAt_pi']
    intro i
    simpa using hdf i x
  case adjoint =>
    intro x
    exact HasAdjoint.pi_rule (K:=K) (f := fun dx i => df i x dx)
      (fun i => hasAdjointUpdate_from_hasAdjoint (hadj i x) (hupd i x))
  case simp => rfl

-- structure Decomposition (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) : Prop where
--   mk_proj : ∀ x, q (p₁ x) (p₂ x) = x
--   proj₁_mk : ∀ x₁ x₂, p₁ (q x₁ x₂) = x₁
--   proj₂_mk : ∀ x₁ x₂, p₂ (q x₁ x₂) = x₂

-- note: this rule still needs the commented out `Decomposition p₁ p₂ q` hypothesis - without it
-- nothing says that `fun x₁ => q x₁ 0` is the adjoint of `p₁`, so the rule is not provable.
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
        (x i, fun dxi dx j => if i=j then dx j + dxi else dx j)) := by
  have hclm : IsContinuousLinearMap K (fun x : I → X => x i) := by fun_prop
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
    (df := fun _ => ContinuousLinearMap.mk' K (fun x : I → X => x i) hclm)
    (df' := fun _ dxi dx j => if i=j then dx j + dxi else dx j)
  case deriv => intro x; exact (ContinuousLinearMap.mk' K (fun x : I → X => x i) hclm).hasFDerivAt
  case adjoint =>
    intro x
    refine hasAdjointUpdate_from_hasAdjoint (HasRevFDeriv.hasAdjoint_apply i) ?_
    intro dxi dx
    funext j
    by_cases h : i = j <;> simp [h, add_comm]
  case simp => rfl

-- this should not be necessary if once we improve function decomposition in `data_synth` tactic
@[data_synth]
theorem apply_rule' {I} {nI} [IndexType I nI] [Fold I] [DecidableEq I] (i : I) :
    HasRevFDerivUpdate K (fun x : (I → X)×Y => x.1 i)
      (fun x =>
        (x.1 i, fun dxi dx => (fun j => if i=j then dx.1 j + dxi else dx.1 j, dx.2))) := by
  have hclm : IsContinuousLinearMap K (fun x : (I → X)×Y => x.1 i) := by fun_prop
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
    (df := fun _ => ContinuousLinearMap.mk' K (fun x : (I → X)×Y => x.1 i) hclm)
    (df' := fun _ dxi dx => (fun j => if i=j then dx.1 j + dxi else dx.1 j, dx.2))
  case deriv => intro x; exact (ContinuousLinearMap.mk' K (fun x : (I → X)×Y => x.1 i) hclm).hasFDerivAt
  case adjoint =>
    intro x
    refine hasAdjointUpdate_from_hasAdjoint (HasRevFDeriv.hasAdjoint_apply' (Y:=Y) i) ?_
    intro dxi dx
    refine Prod.ext ?_ ?_
    · funext j; by_cases h : i = j <;> simp [h, add_comm]
    · simp
  case simp => rfl

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
  choose df hdf df' hadj hupd using fun i => (hf i).deriv
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
    (df := fun x => ContinuousLinearMap.pi (fun i => df i x))
    (df' := fun x dy dx => IndexType.fold .full (init:=dx) fun i dx => (f' i x).2 (dy i) dx)
  case deriv =>
    intro x
    rw [hasFDerivAt_pi']
    intro i
    simpa using hdf i x
  case adjoint =>
    intro x
    exact HasAdjointUpdate.pi_rule (K:=K) (f := fun dx i => df i x dx)
      (fun i => hasAdjointUpdate_from_hasAdjoint (hadj i x) (hupd i x))
  case simp => rfl

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
  have hglin : ∀ x, IsContinuousLinearMap K (g' x).2 := by
    obtain ⟨_, dg, _, ha⟩ := hg.deriv_adjoint
    exact fun x => (ha x).isContinuousLinearMap'
  have ⟨_,_,_,_⟩ := hf.deriv_adjointUpdate
  have ⟨_,_,_,_⟩ := hg.deriv_adjoint
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro x; eta_expand; simp; data_synth
  case simp =>
    simp_all
    -- push smul: the adjoint `(g' x).2` is linear
    funext x
    refine Prod.ext rfl ?_
    funext dy
    dsimp only
    rw [show (starRingEnd K) (f x) * dy = (starRingEnd K) (f x) • dy from (smul_eq_mul ..).symm,
      (hglin x).1.map_smul]

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
  obtain ⟨hval, df, hd, ha⟩ := hf.deriv_adjoint
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (df := fun x => (_root_.ContinuousLinearMap.toSpanSingleton K (-((f x)^2)⁻¹)).comp (df x))
  case deriv =>
    intro x
    exact (hasFDerivAt_inv (hf' x)).comp x (hd x)
  case adjoint =>
    intro x
    have h : ⇑((_root_.ContinuousLinearMap.toSpanSingleton K (-((f x)^2)⁻¹)).comp (df x))
             = fun dx => (-((f x)^2)⁻¹) * (df x dx) := by
      funext dx
      simp [_root_.ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
    rw [h]
    exact HasAdjoint.comp_rule _ _ (ha x) (HMul.hMul.arg_a1.HasAdjoint_simp_rule _)
  case simp =>
    funext x
    simp [hval, map_neg, map_inv₀, map_pow, smul_eq_mul]

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
  obtain ⟨hval, df, hd, ha⟩ := hf.deriv_adjointUpdate
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
    (df := fun x => (_root_.ContinuousLinearMap.toSpanSingleton K (-((f x)^2)⁻¹)).comp (df x))
  case deriv =>
    intro x
    exact (hasFDerivAt_inv (hf' x)).comp x (hd x)
  case adjoint =>
    intro x
    have h : ⇑((_root_.ContinuousLinearMap.toSpanSingleton K (-((f x)^2)⁻¹)).comp (df x))
             = fun dx => (-((f x)^2)⁻¹) * (df x dx) := by
      funext dx
      simp [_root_.ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
    rw [h]
    exact HMul.hMul.arg_a1.HasAdjointUpdate_comp_rule _ _ (ha x)
  case simp =>
    funext x
    simp [hval, map_neg, map_inv₀, map_pow, smul_eq_mul]

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
  -- `f / g` is `f * g⁻¹`, so this follows from the multiplication and the reciprocal rule
  have hginv := HInv.hInv.arg_a0.HasRevFDeriv_rule g g' hg hg'
  have h := HMul.hMul.arg_a0a1.HasRevFDeriv_rule f (fun x => (g x)⁻¹) f' _ hf hginv
  have hfun : (fun x => f x / g x) = (fun x => f x * (g x)⁻¹) := by
    funext x; rw [div_eq_mul_inv]
  rw [hfun]
  refine hasRevFDeriv_from_hasRevFDeriv h ?_
  have hval := hg.val
  funext x
  have hz : conj (g x) ≠ 0 := by
    simpa using (starRingEnd K).injective.ne_iff.mpr (hg' x)
  simp only [hval, div_eq_mul_inv, smul_eq_mul, map_inv₀]
  refine Prod.ext rfl ?_
  funext dy
  field_simp

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
  -- `f / g` is `f * g⁻¹`, so this follows from the multiplication and the reciprocal rule
  have hginv := HInv.hInv.arg_a0.HasRevFDerivUpdate_rule g g' hg hg'
  have h := HMul.hMul.arg_a0a1.HasRevFDerivUpdate_rule f (fun x => (g x)⁻¹) f' _ hf hginv
  have hfun : (fun x => f x / g x) = (fun x => f x * (g x)⁻¹) := by
    funext x; rw [div_eq_mul_inv]
  rw [hfun]
  refine hasRevFDerivUpdate_from_hasRevFDerivUpdate h ?_
  have hval := hg.val
  funext x
  have hz : conj (g x) ≠ 0 := by
    simpa using (starRingEnd K).injective.ne_iff.mpr (hg' x)
  simp only [hval, div_eq_mul_inv, smul_eq_mul, map_inv₀]
  refine Prod.ext rfl ?_
  funext dy dx
  field_simp

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
  obtain ⟨hval, df, hd, ha⟩ := hf.deriv_adjoint
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (df := fun x => (n • (f x)^(n-1)) • df x)
  case deriv =>
    intro x
    exact (hd x).pow n
  case adjoint =>
    intro x
    have h : ⇑((n • (f x)^(n-1)) • df x)
             = fun dx => ((n : K) * (f x)^(n-1)) * (df x dx) := by
      funext dx; simp [smul_eq_mul, nsmul_eq_mul]
    rw [h]
    exact HasAdjoint.comp_rule _ _ (ha x) (HMul.hMul.arg_a1.HasAdjoint_simp_rule _)
  case simp =>
    funext x
    simp [hval, map_mul, map_pow, map_natCast, smul_eq_mul, mul_assoc]

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
  obtain ⟨hval, df, hd, ha⟩ := hf.deriv_adjointUpdate
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
    (df := fun x => (n • (f x)^(n-1)) • df x)
  case deriv =>
    intro x
    exact (hd x).pow n
  case adjoint =>
    intro x
    have h : ⇑((n • (f x)^(n-1)) • df x)
             = fun dx => ((n : K) * (f x)^(n-1)) * (df x dx) := by
      funext dx; simp [smul_eq_mul, nsmul_eq_mul]
    rw [h]
    exact HMul.hMul.arg_a1.HasAdjointUpdate_comp_rule _ _ (ha x)
  case simp =>
    funext x
    simp [hval, map_mul, map_pow, map_natCast, smul_eq_mul, mul_assoc]

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
        (A.sum (fun i => f i), fun dx i => (A : Set I).indicator (fun _ => dx) i)) := by
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
        (A.sum (fun i => f i), fun dx i => (A : Set I).indicator (fun _ => dx) i)) := by
  apply Finset.sum.arg_f.HasRevFDeriv_rule

@[data_synth]
theorem Finset.sum.arg_f.HasRevFDerivUpdate_rule
    {I : Type*} {nI} [IndexType I nI] [Fold I] (A : Finset I) :
    HasRevFDerivUpdate K
      (fun f : I → X => A.sum (fun i => f i))
      (fun f =>
        (A.sum (fun i => f i), fun dx df i => df i + (A : Set I).indicator (fun _ => dx) i)) := by
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
          let dx := dxi + (A : Set I).indicator (fun _ => dx) i
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
  refine hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (df := fun x => fun dx =>L[R]
      ⟪(2 : R) • x, dx⟫[R])
    (df' := fun x dr => dr • ((2 : R) • x)) ?_ ?_ ?_
  · intro x
    simpa [AdjointSpace.inner_smul_left, conj_for_real_scalar] using
      (Norm2.norm2.arg_a0.HasRevFDeriv_simple_rule_real (R := R) (X := X) x)
  · intro x
    simpa [smul_smul] using
      (Inner.inner.arg_a1.HasAdjoint_simple_rule_real
        (R := R) (K := R) ((2 : R) • x))
  · funext x
    simp [smul_smul, mul_comm]

@[data_synth]
theorem Norm2.norm2.arg_a0.HasRevFDerivUpdate_simple_rule :
  HasRevFDerivUpdate R
    (fun x : X => ‖x‖₂²[R])
    (fun x =>
      let s := ‖x‖₂²[R];
      (s, fun dr x' =>
        let dx := (2*dr) • x + x'
        dx)) := by
  refine hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
    (df := fun x => fun dx =>L[R]
      ⟪(2 : R) • x, dx⟫[R])
    (df' := fun x dr x' => x' + dr • ((2 : R) • x)) ?_ ?_ ?_
  · intro x
    simpa [AdjointSpace.inner_smul_left, conj_for_real_scalar] using
      (Norm2.norm2.arg_a0.HasRevFDeriv_simple_rule_real (R := R) (X := X) x)
  · intro x
    simpa [smul_smul] using
      (Inner.inner.arg_a1.HasAdjointUpdate_simple_rule_real
        (R := R) (K := R) ((2 : R) • x))
  · funext x
    ext <;> simp [smul_smul, mul_comm, add_comm]

/-- `y ↦ ‖y‖₂` is differentiable away from zero and its derivative is `dy ↦ ⟪dy,y⟫/‖y‖₂`. -/
theorem norm₂.hasFDerivAt_of_ne_zero (y : Y) (hy : y ≠ 0) :
    HasFDerivAt (fun y : Y => ‖y‖₂[R]) (fun dy =>L[R] ⟪dy,y⟫[R] / ‖y‖₂[R]) y := by
  have h := (norm₂.arg_x.DifferentiableAt_rule (R:=R) (U:=Y) y hy).hasFDerivAt
  rwa [norm₂.arg_x.fderiv_rule_at (R:=R) y hy] at h

/-- Adjoint of `dy ↦ ⟪dy,y⟫/c`. -/
theorem inner_div.hasAdjoint (y : Y) (c : R) :
    HasAdjoint R (fun dy : Y => ⟪dy,y⟫[R] / c) (fun dr : R => (dr / c) • y) := by
  have h := Inner.inner.arg_a1.HasAdjoint_simple_rule (K:=R) (X:=Y) (c⁻¹ • y)
  have e : (fun dy : Y => ⟪(c⁻¹ • y),dy⟫[R]) = (fun dy : Y => ⟪dy,y⟫[R] / c) := by
    funext dy
    rw [AdjointSpace.inner_smul_left, conj_for_real_scalar,
      ← AdjointSpace.conj_symm (𝕜:=R) dy y, conj_for_real_scalar, div_eq_inv_mul]
  rw [e] at h
  have e2 : (fun dr : R => dr • (c⁻¹ • y)) = (fun dr : R => (dr / c) • y) := by
    funext dr; rw [smul_smul, div_eq_mul_inv]
  rwa [e2] at h

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
  obtain ⟨hval, df, hderiv, hadj⟩ := hf
  refine hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (df := fun x => (ContinuousLinearMap.mk' R (fun dy : Y => ⟪dy, f x⟫[R] / ‖f x‖₂[R])
      ((inner_div.hasAdjoint (R:=R) (f x) (‖f x‖₂[R])).is_linear)).comp (df x))
    (df' := fun x dr => (f' x).2 ((dr / ‖f x‖₂[R]) • f x)) ?_ ?_ ?_
  · intro x
    exact (norm₂.hasFDerivAt_of_ne_zero (R:=R) (f x) (hf' x)).comp x (hderiv x)
  · intro x
    exact HasAdjoint.comp_rule _ _ (hadj x) (inner_div.hasAdjoint (R:=R) (f x) (‖f x‖₂[R]))
  · funext x
    simp only [hval x, div_eq_mul_inv]

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
  obtain ⟨hval, df, hderiv, hadj⟩ := hf.deriv_adjointUpdate
  refine hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
    (df := fun x => (ContinuousLinearMap.mk' R (fun dy : Y => ⟪dy, f x⟫[R] / ‖f x‖₂[R])
      ((inner_div.hasAdjoint (R:=R) (f x) (‖f x‖₂[R])).is_linear)).comp (df x))
    (df' := fun x dr dx => (f' x).2 ((dr / ‖f x‖₂[R]) • f x) dx) ?_ ?_ ?_
  · intro x
    exact (norm₂.hasFDerivAt_of_ne_zero (R:=R) (f x) (hf' x)).comp x (hderiv x)
  · intro x
    exact HasAdjointUpdate.comp_rule _ _ (hadj x)
      (inner_div.hasAdjoint (R:=R) (f x) (‖f x‖₂[R]))
  · funext x
    simp only [hval x, div_eq_mul_inv]

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
