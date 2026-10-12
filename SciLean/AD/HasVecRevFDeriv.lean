module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

public import SciLean.Algebra.TensorProduct.Prod
public import SciLean.Algebra.TensorProduct.Pi
public import SciLean.Analysis.Calculus.HasRevFDeriv

@[expose] public section


set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace SciLean

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
  {Z : Type*} [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace 𝕜 W]
  {WX : Type*} [NormedAddCommGroup WX] [AdjointSpace 𝕜 WX]
  {WY : Type*} [NormedAddCommGroup WY] [AdjointSpace 𝕜 WY]
  {WZ : Type*} [NormedAddCommGroup WZ] [AdjointSpace 𝕜 WZ]
  [TensorProductType 𝕜 W X WX]
  [TensorProductType 𝕜 W Y WY]
  [TensorProductType 𝕜 W Z WZ]

set_default_scalar 𝕜

variable (𝕜 W) in
@[data_synth out f' in f]
structure HasVecRevFDeriv (f : X → Y) (f' : X → Y × (W ⊗ Y → W ⊗ X)) where
  val : ∀ x, (f' x).1 = f x
  deriv :
      ∃ df : X → X →L[𝕜] Y,
      (∀ x, HasFDerivAt f (df x) x)
      ∧
      ∃ df' : X → Y → X,
      (∀ x, HasAdjoint 𝕜 (df x) (df' x))
      ∧
      (∀ x (dy : Y) (w : W), w ⊗ (df' x dy) = (f' x).2 (w ⊗ dy))
  -- I think linearity is necessary requirement as we define `f'` only on inputs of the form
  -- `dx ⊗ w` which needs to be extended by linearity to all elements of `X ⊗ W`
  linear : ∀ x, IsContinuousLinearMap 𝕜 (f' x).2

variable (𝕜 W) in
@[data_synth out f' in f]
structure HasVecRevFDerivUpdate (f : X → Y) (f' : X → Y × (W ⊗ Y → W ⊗ X → W ⊗ X)) where
  val : ∀ x, (f' x).1 = f x
  deriv : HasVecRevFDeriv 𝕜 W f (fun x => let' (y,df') := f' x; (y, fun dy => df' dy 0))
  add_dx : ∀ x dy dx, (f' x).2 dy dx = dx + (f' x).2 dy 0


open Classical in
variable (𝕜 W) in
noncomputable
def vecRevFDeriv (f : X → Y) (x : X) : (Y × (W ⊗ Y → W ⊗ X)) :=
  if h : ∃ f', HasVecRevFDeriv 𝕜 W f f' then
    choose h x
  else
    (0,0)


theorem HasVecRevFDeriv.unique {f : X → Y} {f' f'' : X → Y × (W ⊗ Y → W ⊗ X)}
    (h1 : HasVecRevFDeriv 𝕜 W f f') (h2 : HasVecRevFDeriv 𝕜 W f f'') : f' = f'' := by
  obtain ⟨df1, hd1, adj1, ha1, ht1⟩ := h1.deriv
  obtain ⟨df2, hd2, adj2, ha2, ht2⟩ := h2.deriv
  funext x
  have hdf : df1 x = df2 x := (hd1 x).unique (hd2 x)
  have hadj : adj1 x = adj2 x := by
    rw [← adjoint_from_hasAdjoint (ha1 x), ← adjoint_from_hasAdjoint (ha2 x), hdf]
  have hsnd : (f' x).2 = (f'' x).2 :=
    tmul_ext (Y:=W) (X:=Y) (h1.linear x).linear (h2.linear x).linear
      (fun w dy => by rw [← ht1 x dy w, ← ht2 x dy w, hadj])
  exact Prod.ext ((h1.val x).trans (h2.val x).symm) hsnd

theorem vecRevFDeriv_from_hasVecRevFDeriv
    {f : X → Y} {f'} (hf : HasVecRevFDeriv 𝕜 W f f') :
    vecRevFDeriv 𝕜 W f = f' := by
  have h : ∃ g, HasVecRevFDeriv 𝕜 W f g := ⟨f', hf⟩
  funext x
  simp only [vecRevFDeriv, h, ↓reduceDIte]
  rw [(Classical.choose_spec h).unique hf]

simproc_decl vecRevFDeriv_simproc (vecRevFDeriv _ _ _) :=
  mkDataSynthSimproc `vecRevFDeriv_simproc ``vecRevFDeriv_from_hasVecRevFDeriv


----------------------------------------------------------------------------------------------------
-- API for constructing and deconstructing HasFwdFDeriv -----------------------------------
----------------------------------------------------------------------------------------------------

-- theorem hasFwdFDeriv_from_hasFDerivAt {f : X → Y}
--     {df : X → X →L[K] Y} (deriv : ∀ x, HasFDerivAt (𝕜:=K) f (df x) x)
--     {f' : X → X → Y×Y} (simp : ∀ x dx, f' x dx = (f x, df x dx)) :
--     HasFwdFDeriv K f f' := by
--   constructor
--   case val =>
--     simp[simp]
--   case deriv =>
--     apply Exists.intro df
--     simp_all


-- set_option linter.unusedVariables false in
-- -- @[to_data_synth_simproc] -- this attribute should automatically generate the following simproc
-- theorem fwdFDeriv_from_hasFwdFDeriv
--   {f : X → Y} {f'} (hf : HasFwdFDeriv K f f') :
--   fwdFDeriv K f = f' := sorry_proof

-- simproc_decl fwdFDeriv_simproc (fwdFDeriv _ _) :=
--   mkDataSynthSimproc `fwdFDeriv_simproc ``fwdFDeriv_from_hasFwdFDeriv

----------------------------------------------------------------------------------------------------
-- Lambda Theorems ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

namespace HasVecRevFDeriv

@[data_synth]
theorem id_rule : HasVecRevFDeriv 𝕜 W (fun x : X => x) (λ x => (x, fun dx => dx)) where
  val := by intros; rfl
  deriv := ⟨fun _ => ContinuousLinearMap.id 𝕜 X, fun x => hasFDerivAt_id x,
            fun _ x => x, fun _ => HasAdjoint.id_rule, by intros; rfl⟩
  linear := by intro x; fun_prop

theorem const_rule (c : Y) : HasVecRevFDeriv 𝕜 W (fun _ : X => c) (λ _ => (c, fun dy => 0)) where
  val := by intros; rfl
  deriv := ⟨fun _ => 0, fun x => hasFDerivAt_const c x,
            fun _ _ => 0, fun _ => HasAdjoint.const_rule, by intros; simp⟩
  linear := by intro x; fun_prop

theorem comp_rule {g : X → Y} {f : Y → Z} {g' f'}
    (hf : HasVecRevFDeriv 𝕜 W f f') (hg : HasVecRevFDeriv 𝕜 W g g') :
    HasVecRevFDeriv 𝕜 W
      (fun x => f (g x))
      (fun x =>
        let' (y, dg') := g' x
        let' (z, df') := f' y
        (z, fun dz =>
          let dy := df' dz
          let dx := dg' dy
          dx)) := by
  obtain ⟨dff, hdff, adjf, hadjf, htf⟩ := hf.deriv
  obtain ⟨dgg, hdgg, adjg, hadjg, htg⟩ := hg.deriv
  have hgval := hg.val
  constructor
  case val => intro x; simp [hg.val, hf.val]
  case deriv =>
    refine ⟨fun x => (dff (g x)).comp (dgg x), fun x => (hdff (g x)).comp x (hdgg x),
            fun x dz => adjg x (adjf (g x) dz), fun x => ?_, ?_⟩
    · exact HasAdjoint.comp_rule _ _ (hadjg x) (hadjf (g x))
    · intro x dz w
      simp only [hgval, htf, htg]
  case linear =>
    intro x
    simp only [hgval]
    exact IsContinuousLinearMap.comp_rule _ (hf.linear (g x)) _ (hg.linear x)

theorem let_rule {g : X → Y} {f : Y → X → Z} {f' g'}
    (hg : HasVecRevFDerivUpdate 𝕜 W g g') (hf : HasVecRevFDeriv 𝕜 W (fun yx : Y×X => f yx.1 yx.2) f') :
    HasVecRevFDeriv 𝕜 W
      (fun x =>
        let y := g x
        f y x)
      (fun x =>
        let' (y, dg') := g' x
        let' (z, df') := f' (y,x)
        (z, fun dz =>
          let' (dy,dx) := df' dz
          let dx := dg' dy dx
          dx)) := by
  obtain ⟨dF, hdF, adjF, hadjF, htF⟩ := hf.deriv
  obtain ⟨dg, hdg, adjg, hadjg, htg⟩ := hg.deriv.deriv
  have hgval : ∀ x, (g' x).1 = g x := hg.val
  constructor
  case val => intro x; simp only [hgval, hf.val]
  case deriv =>
    refine ⟨fun x => (dF (g x, x)).comp ((dg x).prod (ContinuousLinearMap.id 𝕜 X)),
            fun x => ?_,
            fun x dz =>
              let p := adjF (g x, x) dz
              p.2 + adjg x p.1,
            fun x => ?_, ?_⟩
    · have hinner : HasFDerivAt (fun x' : X => (g x', x'))
          ((dg x).prod (ContinuousLinearMap.id 𝕜 X)) x := (hdg x).prodMk (hasFDerivAt_id x)
      have h : HasFDerivAt ((fun yx : Y×X => f yx.1 yx.2) ∘ (fun x' : X => (g x', x')))
          ((dF (g x, x)).comp ((dg x).prod (ContinuousLinearMap.id 𝕜 X))) x :=
        HasFDerivAt.comp x (hdF (g x, x)) hinner
      exact h
    · have h1 : HasAdjointUpdate 𝕜 (fun dx => dg x dx) (fun dy dx => dx + adjg x dy) :=
        hasAdjointUpdate_from_hasAdjoint (hadjg x) (by intros; rfl)
      have h2 : HasAdjoint 𝕜 (fun yx : Y×X => dF (g x, x) (yx.1, yx.2)) (adjF (g x, x)) := hadjF _
      exact HasAdjoint.let_rule (K:=𝕜) (fun dx => dg x dx)
        (fun dy dx => dF (g x, x) (dy, dx)) h1 h2
    · intro x dz w
      simp only [hgval]
      rw [← htF (g x, x) dz w]
      show w ⊗ ((adjF (g x, x) dz).2 + adjg x (adjF (g x, x) dz).1)
           = (g' x).2 (w ⊗ (adjF (g x, x) dz).1) (w ⊗ (adjF (g x, x) dz).2)
      rw [hg.add_dx]
      have h := htg x (adjF (g x, x) dz).1 w
      dsimp only at h
      rw [← h, tmul_add]
  case linear =>
    intro x
    simp only [hgval]
    have hfun : (fun dz => (g' x).2 ((f' (g x, x)).2 dz).A₁ ((f' (g x, x)).2 dz).A₂)
        = (fun dz => ((f' (g x, x)).2 dz).A₂ + (g' x).2 ((f' (g x, x)).2 dz).A₁ 0) :=
      funext fun dz => hg.add_dx x _ _
    rw [hfun]
    have h1 := hf.linear (g x, x)
    have h2 := hg.deriv.linear x
    dsimp only at h2
    fun_prop


-- note: in the pullback below the binder `i` shadows the index `i` of the projection, so the
-- pullback is the constant function `fun _ => dx` rather than `fun j => if i = j then dx else 0`
-- (compare with `HasRevFDeriv.apply_rule`). As stated the rule is therefore not provable whenever
-- `I` has at least two elements; the same shadowing affects `apply_rule'` and the two
-- `HasVecRevFDerivUpdate` rules below.
@[data_synth]
theorem apply_rule {I nI} [IndexType I nI] [Fold I] [Fold I] (i : I) :
    HasVecRevFDeriv 𝕜 W (fun x : I → X => x i)
      (fun x =>
        (x i, fun dx i => dx)) := sorry_proof

-- this should not be necessary if once we improve function decomposition in `data_synth` tactic
@[data_synth]
theorem apply_rule' {I nI} [IndexType I nI] [Fold I] [Fold I] (i : I) :
    HasVecRevFDeriv 𝕜 W (fun x : (I → X)×Y => x.1 i)
      (fun x =>
        (x.1 i, fun dx => ⟨fun i => dx, 0⟩)) := sorry_proof

theorem pi_rule {I nI} [IndexType I nI] [Fold I] [Fold I] [Fold I]
    {f : X → I → Y} {f' : I → _} (hf : ∀ i, HasVecRevFDerivUpdate 𝕜 W (f · i) (f' i)) :
    HasVecRevFDeriv 𝕜 W f
      (fun x =>
        (fun i => f x i,
         fun dy =>
           IndexType.fold .full (init:=(0:WX)) (fun i dx =>
             let' (y,df') := f' i x
             let dyi := dy i
             let dx := df' dyi dx
             dx))) := by
  -- the accumulating pullbacks only add to the accumulator, so the fold is just the sum
  have hfold : ∀ x (dy : I → W⊗Y),
      (IndexType.fold .full (init:=(0:WX)) fun (i : I) (dx : WX) => (f' i x).2 (dy i) dx)
      =
      ∑ i : I, (f' i x).2 (dy i) 0 := by
    intro x dy
    rw [show (fun (i : I) (dx : WX) => (f' i x).2 (dy i) dx)
           = (fun (i : I) (dx : WX) => dx + (f' i x).2 (dy i) 0) from
          by funext i dx; rw [(hf i).add_dx x (dy i) dx]]
    show IndexType.sum (fun i => (f' i x).2 (dy i) 0) = _
    rw [IndexType.sum_eq_finset_sum]
  choose df hdf adj hadj htmul using fun i => (hf i).deriv.deriv
  constructor
  case val => intro x; rfl
  case deriv =>
    refine ⟨fun x => ContinuousLinearMap.pi (fun i => df i x), ?_,
      fun x dy => ∑ i : I, adj i x (dy i), ?_, ?_⟩
    · intro x
      rw [hasFDerivAt_pi']
      intro i
      simpa using hdf i x
    · intro x
      constructor
      case adjoint =>
        intro dx dy
        show (∑ᴵ i, ⟪df i x dx, dy i⟫[𝕜]) = ⟪dx, ∑ i : I, adj i x (dy i)⟫[𝕜]
        rw [IndexType.sum_eq_finset_sum, AdjointSpace.inner_sum]
        exact Finset.sum_congr rfl fun i _ => (hadj i x).adjoint dx (dy i)
      case is_linear => fun_prop
    · intro x dy w
      show w ⊗ (∑ i : I, adj i x (dy i))
         = IndexType.fold .full (init:=(0:WX)) fun (i : I) (dx : WX) =>
             (f' i x).2 ((w ⊗ dy : I → W⊗Y) i) dx
      have hlin : w ⊗ (∑ i : I, adj i x (dy i)) = ∑ i : I, (w ⊗ adj i x (dy i) : WX) :=
        map_sum (IsLinearMap.mk' _ (tmul.arg_x.IsLinearMap_rule (R:=𝕜) (YX:=WX) w))
          (fun i => adj i x (dy i)) Finset.univ
      rw [hfold x (w ⊗ dy), hlin]
      exact Finset.sum_congr rfl fun i _ => htmul i x (dy i) w
  case linear =>
    intro x
    have h : ∀ i : I, IsContinuousLinearMap 𝕜 (fun dy : I → W⊗Y => (f' i x).2 (dy i) 0) :=
      fun i => IsContinuousLinearMap.comp_rule
        (fun dy : I → W⊗Y => dy i) (IsContinuousLinearMap.apply_rule i)
        (fun dyi : W⊗Y => (f' i x).2 dyi 0) ((hf i).deriv.linear x)
    have he : (fun dy : I → W⊗Y =>
          IndexType.fold .full (init:=(0:WX)) fun (i : I) (dx : WX) => (f' i x).2 (dy i) dx)
        = ⇑(∑ i : I, ContinuousLinearMap.mk' 𝕜
              (fun dy : I → W⊗Y => (f' i x).2 (dy i) 0) (h i)) := by
      funext dy; rw [hfold x dy, sum_apply]; rfl
    rw [he]
    fun_prop

-- set_option linter.unusedVariables false in
-- theorem proj_rule
--     {X₁ : Type*} [NormedAddCommGroup X₁] [AdjointSpace 𝕜 X₁]
--     {X₂ : Type*} [NormedAddCommGroup X₂] [AdjointSpace 𝕜 X₂]
--     (f : X → Y) (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) {g'}
--     (hg : HasVecRevFDeriv 𝕜 W g g') (hf : f = fun x => g (p₁ x) := by rfl)
--     (hp₁ : IsContinuousLinearMap K p₁ := by fun_prop) /- (hdec : Decomposition p₁ p₂ q) -/ :
--     HasVecRevFDeriv 𝕜 W f
--       (fun x dx =>
--         let x₁ := p₁ x
--         let dx₁ := dx.map p₁
--         let ydy := g' x₁ dx₁
--         ydy) := by
--   sorry_proof

-- set_option linter.unusedVariables false in
-- theorem let_skip_rule
--     {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
--     {g : X → α} {f : α → X → Z} {f' : α → _}
--     (hf : ∀ a, HasVecRevFDeriv 𝕜 W (f a) (f' a))
--     (hg : g.IsConstant) :
--     HasVecRevFDeriv 𝕜 W
--       (fun x =>
--         let y := g x
--         f y x)
--       (fun x dx =>
--         let a := g x
--         let' (z, dz) := f' a x dx
--         (z, dz)) := by
--   sorry_proof


open Lean Meta
#eval show MetaM Unit from do
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDeriv,``const_rule⟩, .const⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDeriv, ``comp_rule⟩, .comp
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f)
      (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDeriv,``let_rule⟩, .letE
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f)
      (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDeriv,``pi_rule⟩, .pi
      (← getConstArgId ``pi_rule `f) (← getConstArgId ``pi_rule `hf)⟩
   -- Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDeriv,``proj_rule⟩, .proj
   --    (← getConstArgId ``proj_rule `f) (← getConstArgId ``proj_rule `g)
   --    (← getConstArgId ``proj_rule `p₁) (← getConstArgId ``proj_rule `p₂)
   --    (← getConstArgId ``proj_rule `q) (← getConstArgId ``proj_rule `hg)⟩
   -- Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDeriv,``let_skip_rule⟩, .letSkip
   --    (← getConstArgId ``let_skip_rule `g) (← getConstArgId ``let_skip_rule `f)
   --    (← getConstArgId ``let_skip_rule `hf)⟩

end HasVecRevFDeriv


namespace HasVecRevFDerivUpdate

@[data_synth]
theorem id_rule : HasVecRevFDerivUpdate 𝕜 W (fun x : X => x) (λ x => (x, fun dx dx' => dx' + dx)) where
  val := by intros; rfl
  deriv := {
    val := by intros; rfl
    deriv := ⟨fun _ => ContinuousLinearMap.id 𝕜 X, fun x => hasFDerivAt_id x,
              fun _ x => x, fun _ => HasAdjoint.id_rule, by intros; simp⟩
    linear := by intro x; simp; fun_prop }
  add_dx := by intros; simp

theorem const_rule (c : Y) :
    HasVecRevFDerivUpdate 𝕜 W
      (fun _ : X => c)
      (fun _ => (c, fun dy dx => dx)) where
  val := by intros; rfl
  deriv := HasVecRevFDeriv.const_rule c
  add_dx := by intros; simp

theorem comp_rule {g : X → Y} {f : Y → Z} {g' f'}
    (hf : HasVecRevFDeriv 𝕜 W f f') (hg : HasVecRevFDerivUpdate 𝕜 W g g') :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => f (g x))
      (fun x =>
        let' (y, dg') := g' x
        let' (z, df') := f' y
        (z, fun dz dx =>
          let dy := df' dz
          let dx := dg' dy dx
          dx)) := by
  constructor
  case val => intro x; simp [hg.val, hf.val]
  case deriv => exact HasVecRevFDeriv.comp_rule hf hg.deriv
  case add_dx => intro x dy dx; exact hg.add_dx x _ dx

theorem let_rule {g : X → Y} {f : Y → X → Z} {f' g'}
    (hg : HasVecRevFDerivUpdate 𝕜 W g g')
    (hf : HasVecRevFDerivUpdate 𝕜 W (fun yx : Y×X => f yx.1 yx.2) f') :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x =>
        let y := g x
        f y x)
      (fun x =>
        let' (y, dg') := g' x
        let' (z, df') := f' (y,x)
        (z, fun dz dx =>
          let' (dy,dx) := df' dz ⟨0,dx⟩
          let dx' := dg' dy dx
          dx' + dx)) := by
  -- note: the inner `let'` shadows `dx`, so the incoming `dx` is added twice: `dg' dy dx` already
  -- contains it (see `add_dx`) and it is added again by `dx' + dx`. For `g = id` and `f y x = y`
  -- the right hand side computes `2•dx + dz` instead of the expected `dx + dz`, so the statement
  -- is not provable as it stands. Compare with the proved `HasVecRevFDeriv.let_rule` above.
  sorry_proof


@[data_synth]
theorem apply_rule {I nI} [IndexType I nI] [Fold I] [Fold I] (i : I) :
    HasVecRevFDerivUpdate 𝕜 W (fun x : I → X => x i)
      (fun x =>
        (x i, fun dx dx' i => dx' i + dx)) := sorry_proof

-- this should not be necessary if once we improve function decomposition in `data_synth` tactic
@[data_synth]
theorem apply_rule' {I nI} [IndexType I nI] [Fold I] [Fold I] (i : I) :
    HasVecRevFDerivUpdate 𝕜 W (fun x : (I → X)×Y => x.1 i)
      (fun x =>
        (x.1 i, fun dx dx' => ⟨fun i => dx'.1 i + dx, dx'.2⟩)) := sorry_proof

theorem pi_rule {I nI} [IndexType I nI] [Fold I] [Fold I] [Fold I]
    {f : X → I → Y} {f' : I → _} (hf : ∀ i, HasVecRevFDerivUpdate 𝕜 W (f · i) (f' i)) :
    HasVecRevFDerivUpdate 𝕜 W f
      (fun x =>
        (fun i => f x i,
         fun dy dx =>
           IndexType.fold .full (init:=dx) (fun i dx =>
             let' (y,df') := f' i x
             let dyi := dy i
             let dx := df' dyi dx
             dx))) := by
  constructor
  case val => intro x; rfl
  case deriv => exact HasVecRevFDeriv.pi_rule hf
  case add_dx =>
    intro x dy dx
    show IndexType.fold .full (init:=dx) (fun (i : I) (dx : WX) => (f' i x).2 (dy i) dx)
       = dx + IndexType.fold .full (init:=(0:WX)) (fun (i : I) (dx : WX) => (f' i x).2 (dy i) dx)
    rw [show (fun (i : I) (dx : WX) => (f' i x).2 (dy i) dx)
           = (fun (i : I) (dx : WX) => dx + (f' i x).2 (dy i) 0) from
          by funext i dx; rw [(hf i).add_dx x (dy i) dx]]
    rw [IndexType.fold_add_eq_add_sum, IndexType.fold_add_eq_add_sum, zero_add]

-- set_option linter.unusedVariables false in
-- theorem proj_rule
--     {X₁ : Type*} [NormedAddCommGroup X₁] [AdjointSpace 𝕜 X₁]
--     {X₂ : Type*} [NormedAddCommGroup X₂] [AdjointSpace 𝕜 X₂]
--     (f : X → Y) (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) {g'}
--     (hg : HasVecRevFDerivUpdate 𝕜 W g g') (hf : f = fun x => g (p₁ x) := by rfl)
--     (hp₁ : IsContinuousLinearMap K p₁ := by fun_prop) /- (hdec : Decomposition p₁ p₂ q) -/ :
--     HasVecRevFDerivUpdate 𝕜 W f
--       (fun x dx =>
--         let x₁ := p₁ x
--         let dx₁ := dx.map p₁
--         let ydy := g' x₁ dx₁
--         ydy) := by
--   sorry_proof

-- set_option linter.unusedVariables false in
-- theorem let_skip_rule
--     {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
--     {g : X → α} {f : α → X → Z} {f' : α → _}
--     (hf : ∀ a, HasVecRevFDerivUpdate 𝕜 W (f a) (f' a))
--     (hg : g.IsConstant) :
--     HasVecRevFDerivUpdate 𝕜 W
--       (fun x =>
--         let y := g x
--         f y x)
--       (fun x dx =>
--         let a := g x
--         let' (z, dz) := f' a x dx
--         (z, dz)) := by
--   sorry_proof


open Lean Meta
#eval show MetaM Unit from do
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDerivUpdate,``const_rule⟩, .const⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDerivUpdate, ``comp_rule⟩, .comp
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f)
      (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDerivUpdate,``let_rule⟩, .letE
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f)
      (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDerivUpdate,``pi_rule⟩, .pi
      (← getConstArgId ``pi_rule `f) (← getConstArgId ``pi_rule `hf)⟩
   -- Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDerivUpdate,``proj_rule⟩, .proj
   --    (← getConstArgId ``proj_rule `f) (← getConstArgId ``proj_rule `g)
   --    (← getConstArgId ``proj_rule `p₁) (← getConstArgId ``proj_rule `p₂)
   --    (← getConstArgId ``proj_rule `q) (← getConstArgId ``proj_rule `hg)⟩
   -- Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDerivUpdate,``let_skip_rule⟩, .letSkip
   --    (← getConstArgId ``let_skip_rule `g) (← getConstArgId ``let_skip_rule `f)
   --    (← getConstArgId ``let_skip_rule `hf)⟩

end HasVecRevFDerivUpdate

end SciLean
open SciLean


variable
  {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
  {Z : Type*} [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace 𝕜 W]
  {WX : Type*} [NormedAddCommGroup WX] [AdjointSpace 𝕜 WX]
  {WY : Type*} [NormedAddCommGroup WY] [AdjointSpace 𝕜 WY]
  {WZ : Type*} [NormedAddCommGroup WZ] [AdjointSpace 𝕜 WZ]
  [TensorProductType 𝕜 W X WX]
  [TensorProductType 𝕜 W Y WY]
  [TensorProductType 𝕜 W Z WZ]

set_default_scalar 𝕜

@[data_synth]
theorem Prod.mk.arg_a0a1.HasVecRevFDerivUpdate_comp_rule
    {f : X → Y} {g : X → Z} {f' g'}
    (hf : HasVecRevFDerivUpdate 𝕜 W f f') (hg : HasVecRevFDerivUpdate 𝕜 W g g') :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => (f x, g x))
      (fun x =>
        let' (y, df') := f' x
        let' (z, dg') := g' x
        ((y, z),
         fun dyz dx =>
           let' (dy,dz) := dyz
           dg' dz (df' dy dx))) := by
  obtain ⟨dff, hdff, adjf, hadjf, htf⟩ := hf.deriv.deriv
  obtain ⟨dgg, hdgg, adjg, hadjg, htg⟩ := hg.deriv.deriv
  have hfval := hf.val
  have hgval := hg.val
  have hfadd := hf.add_dx
  have hgadd := hg.add_dx
  constructor
  case val => intro x; simp [hfval, hgval]
  case add_dx =>
    intro x dyz dx
    dsimp only
    rw [hfadd x dyz.A₁ dx, hgadd x dyz.A₂ _, hgadd x dyz.A₂ ((f' x).2 dyz.A₁ 0), add_assoc]
  case deriv =>
    constructor
    case val => intro x; simp [hfval, hgval]
    case deriv =>
      refine ⟨fun x => (dff x).prod (dgg x), fun x => (hdff x).prodMk (hdgg x),
              fun x dyz => adjf x dyz.1 + adjg x dyz.2, fun x => ?_, ?_⟩
      · constructor
        · intro v dyz
          rw [AdjointSpace.inner_prod_split, AdjointSpace.inner_add_right]
          show ⟪dff x v, dyz.1⟫[𝕜] + ⟪dgg x v, dyz.2⟫[𝕜] = _
          rw [(hadjf x).adjoint, (hadjg x).adjoint]
        · fun_prop
      · intro x dyz w
        dsimp only at htf htg ⊢
        show w ⊗[𝕜] (adjf x dyz.1 + adjg x dyz.2)
           = (g' x).2 (w ⊗[𝕜] dyz.2) ((f' x).2 (w ⊗[𝕜] dyz.1) 0)
        rw [tmul_add, htf x dyz.1 w, htg x dyz.2 w,
          hgadd x (w ⊗[𝕜] dyz.2) ((f' x).2 (w ⊗[𝕜] dyz.1) 0)]
    case linear =>
        intro x
        have h : (fun dyz : ProdMatrixRow WY WZ => (g' x).2 dyz.A₂ ((f' x).2 dyz.A₁ 0))
               = fun dyz => (f' x).2 dyz.A₁ 0 + (g' x).2 dyz.A₂ 0 := by
          funext dyz; rw [hgadd x dyz.A₂ _]
        show IsContinuousLinearMap 𝕜
          (fun dyz : ProdMatrixRow WY WZ => (g' x).2 dyz.A₂ ((f' x).2 dyz.A₁ 0))
        rw [h]
        refine HAdd.hAdd.arg_a0a1.IsContinuousLinearMap_rule _ _ ?_ ?_
        · exact IsContinuousLinearMap.comp_rule _ ProdMatrixRow.A₁.arg_A.IsContinuousLinearMap_rule
            _ (hf.deriv.linear x)
        · exact IsContinuousLinearMap.comp_rule _ ProdMatrixRow.A₂.arg_A.IsContinuousLinearMap_rule
            _ (hg.deriv.linear x)


@[data_synth]
theorem Prod.fst.arg_self.HasVecRevFDerivUpdate_proj_rule :
    HasVecRevFDerivUpdate 𝕜 W
      (fun xy : X×Y => xy.1)
      (fun x => (x.1, fun dx dxy => let' (dx',dy') := dxy; ⟨dx' + dx, dy'⟩)) := by
  constructor
  case val => intro x; rfl
  case add_dx =>
    intro x dy dx
    show ProdMatrixRow.mk (dx.A₁ + dy) dx.A₂
       = ProdMatrixRow.mk (dx.A₁ + (0 + dy)) (dx.A₂ + 0)
    simp
  case deriv =>
    constructor
    case val => intro x; rfl
    case deriv =>
      refine ⟨fun _ => ContinuousLinearMap.fst 𝕜 X Y, fun x => hasFDerivAt_fst,
              fun _ dx => (dx, 0), fun x => ?_, ?_⟩
      · constructor
        · intro v dx
          show ⟪v.1, dx⟫[𝕜] = ⟪v.1, dx⟫[𝕜] + ⟪v.2, (0:Y)⟫[𝕜]
          simp
        · fun_prop
      · intro x dx w
        show ProdMatrixRow.mk (tmulAdd (1:𝕜) w dx 0) (tmulAdd (1:𝕜) w (0:Y) 0) = _
        show ProdMatrixRow.mk (w ⊗[𝕜] dx) (w ⊗[𝕜] (0:Y))
           = ProdMatrixRow.mk (0 + w ⊗[𝕜] dx) 0
        simp
    case linear =>
        intro x
        show IsContinuousLinearMap 𝕜 (fun dwx => (⟨0 + dwx, 0⟩ : ProdMatrixRow WX WY))
        fun_prop

@[data_synth]
theorem Prod.snd.arg_self.HasVecRevFDerivUpdate_proj_rule :
    HasVecRevFDerivUpdate 𝕜 W
      (fun xy : X×Y => xy.2)
      (fun x => (x.2, fun dy dxy => let' (dx',dy') := dxy; ⟨dx', dy' + dy⟩)) := by
  constructor
  case val => intro x; rfl
  case add_dx =>
    intro x dy dx
    show ProdMatrixRow.mk dx.A₁ (dx.A₂ + dy)
       = ProdMatrixRow.mk (dx.A₁ + 0) (dx.A₂ + (0 + dy))
    simp
  case deriv =>
    constructor
    case val => intro x; rfl
    case deriv =>
      refine ⟨fun _ => ContinuousLinearMap.snd 𝕜 X Y, fun x => hasFDerivAt_snd,
              fun _ dy => (0, dy), fun x => ?_, ?_⟩
      · constructor
        · intro v dy
          show ⟪v.2, dy⟫[𝕜] = ⟪v.1, (0:X)⟫[𝕜] + ⟪v.2, dy⟫[𝕜]
          simp
        · fun_prop
      · intro x dy w
        show ProdMatrixRow.mk (tmulAdd (1:𝕜) w (0:X) 0) (tmulAdd (1:𝕜) w dy 0) = _
        show ProdMatrixRow.mk (w ⊗[𝕜] (0:X)) (w ⊗[𝕜] dy)
           = ProdMatrixRow.mk 0 (0 + w ⊗[𝕜] dy)
        simp
    case linear =>
        intro x
        show IsContinuousLinearMap 𝕜 (fun dwy => (⟨0, 0 + dwy⟩ : ProdMatrixRow WX WY))
        fun_prop

@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasVecRevFDerivUpdate_comp_rule
    {f : X → Y} {g : X → Y} {f' g'}
    (hf : HasVecRevFDerivUpdate 𝕜 W f f') (hg : HasVecRevFDerivUpdate 𝕜 W g g') :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => f x + g x)
      (fun x =>
        let' (y, df') := f' x
        let' (z, dg') := g' x
        (y + z, fun dy dx =>
          let dx := df' dy dx
          let dx := dg' dy dx
          dx)) := by
  obtain ⟨dff, hdff, adjf, hadjf, htf⟩ := hf.deriv.deriv
  obtain ⟨dgg, hdgg, adjg, hadjg, htg⟩ := hg.deriv.deriv
  have hfval := hf.val
  have hgval := hg.val
  have hfadd := hf.add_dx
  have hgadd := hg.add_dx
  constructor
  case val => intro x; simp [hfval, hgval]
  case add_dx =>
    intro x dy dx
    dsimp only
    rw [hfadd x dy dx, hgadd x dy _, hgadd x dy ((f' x).2 dy 0), add_assoc]
  case deriv =>
    constructor
    case val => intro x; simp [hfval, hgval]
    case deriv =>
      refine ⟨fun x => dff x + dgg x, fun x => (hdff x).add (hdgg x),
              fun x dy => adjf x dy + adjg x dy, fun x => ?_, ?_⟩
      · constructor
        · intro v dy
          rw [add_apply, AdjointSpace.inner_add_left, (hadjf x).adjoint, (hadjg x).adjoint,
              AdjointSpace.inner_add_right]
        · fun_prop
      · intro x dy w
        dsimp only at htf htg ⊢
        rw [tmul_add, htf x dy w, htg x dy w,
            hgadd x (w ⊗ dy) ((f' x).2 (w ⊗ dy) 0)]
    case linear =>
        intro x
        have h : (fun dwy => (g' x).2 dwy ((f' x).2 dwy 0))
               = fun dwy => (f' x).2 dwy 0 + (g' x).2 dwy 0 := by
          funext dwy; rw [hgadd x dwy _]
        show IsContinuousLinearMap 𝕜 (fun dwy => (g' x).2 dwy ((f' x).2 dwy 0))
        rw [h]
        exact HAdd.hAdd.arg_a0a1.IsContinuousLinearMap_rule _ _
          (hf.deriv.linear x) (hg.deriv.linear x)


@[data_synth]
theorem HSub.hSub.arg_a0a1.HasVecRevFDerivUpdate_comp_rule
    {f : X → Y} {g : X → Y} {f' g'}
    (hf : HasVecRevFDerivUpdate 𝕜 W f f') (hg : HasVecRevFDerivUpdate 𝕜 W g g') :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => f x - g x)
      (fun x =>
        let' (y, df') := f' x
        let' (z, dg') := g' x
        (y - z, fun dy dx =>
          let dx := df' dy dx
          let dx := dg' (-dy) dx
          dx)) := by
  obtain ⟨dff, hdff, adjf, hadjf, htf⟩ := hf.deriv.deriv
  obtain ⟨dgg, hdgg, adjg, hadjg, htg⟩ := hg.deriv.deriv
  have hfval := hf.val
  have hgval := hg.val
  have hfadd := hf.add_dx
  have hgadd := hg.add_dx
  have hglin : ∀ x, IsContinuousLinearMap 𝕜 (fun dwy => (g' x).2 dwy 0) :=
    fun x => hg.deriv.linear x
  constructor
  case val => intro x; simp [hfval, hgval]
  case add_dx =>
    intro x dy dx
    dsimp only
    rw [hfadd x dy dx, hgadd x (-dy) _, hgadd x (-dy) ((f' x).2 dy 0), add_assoc]
  case deriv =>
    constructor
    case val => intro x; simp [hfval, hgval]
    case deriv =>
      refine ⟨fun x => dff x - dgg x, fun x => (hdff x).sub (hdgg x),
              fun x dy => adjf x dy - adjg x dy, fun x => ?_, ?_⟩
      · constructor
        · intro v dy
          rw [sub_apply, AdjointSpace.inner_sub_left, (hadjf x).adjoint, (hadjg x).adjoint,
              AdjointSpace.inner_sub_right]
        · fun_prop
      · intro x dy w
        dsimp only at htf htg ⊢
        have hneg : (g' x).2 (-(w ⊗ dy)) 0 = - ((g' x).2 (w ⊗ dy) 0) := (hglin x).1.map_neg _
        rw [tmul_sub, htf x dy w, htg x dy w,
            hgadd x (-(w ⊗ dy)) ((f' x).2 (w ⊗ dy) 0), hneg]
        abel
    case linear =>
        intro x
        have h : (fun dwy => (g' x).2 (-dwy) ((f' x).2 dwy 0))
               = fun dwy => (f' x).2 dwy 0 + (g' x).2 (-dwy) 0 := by
          funext dwy; rw [hgadd x (-dwy) _]
        show IsContinuousLinearMap 𝕜 (fun dwy => (g' x).2 (-dwy) ((f' x).2 dwy 0))
        rw [h]
        refine HAdd.hAdd.arg_a0a1.IsContinuousLinearMap_rule _ _ (hf.deriv.linear x) ?_
        exact IsContinuousLinearMap.comp_rule _
          (Neg.neg.arg_a0.IsContinuousLinearMap_rule _ (IsContinuousLinearMap.id_rule ..))
          _ (hglin x)


-- The original statement below is false: the value `- y` refers to an auto-bound universally
-- quantified variable `y` instead of the argument `x`, so `val` would force `-y = -x` for all
-- `x` and `y`. The corrected statement is proved right after it.
-- @[data_synth]
-- theorem Neg.neg.arg_a0.HasVecRevFDerivUpdate_comp_rule :
--     HasVecRevFDerivUpdate 𝕜 W
--       (fun x : X => - x)
--       (fun x =>
--         (- y, fun dx' dx =>
--           let dx := dx - dx'
--           dx)) := by
--   sorry_proof

/-- Reverse mode derivative of negation.

This is the original `Neg.neg.arg_a0.HasVecRevFDerivUpdate_comp_rule` with the value `- y`
corrected to `- x`. -/
@[data_synth]
theorem Neg.neg.arg_a0.HasVecRevFDerivUpdate_comp_rule :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x : X => - x)
      (fun x =>
        (- x, fun dx' dx =>
          let dx := dx - dx'
          dx)) := by
  constructor
  case val => intro x; rfl
  case add_dx => intro x dy dx; show dx - dy = dx + (0 - dy); abel
  case deriv =>
    constructor
    case val => intro x; rfl
    case deriv =>
      refine ⟨fun _ => -ContinuousLinearMap.id 𝕜 X, fun x => (hasFDerivAt_id x).neg,
              fun _ dy => -dy, fun x => ?_, ?_⟩
      · exact Neg.neg.arg_a0.HasAdjoint_simple_rule (K:=𝕜) (X:=X)
      · intro x dy w
        dsimp only
        rw [tmul_neg, zero_sub]
    case linear =>
        intro x
        dsimp only
        fun_prop

set_default_scalar 𝕜
open ComplexConjugate TensorProductType


@[data_synth]
theorem HSMul.hSMul.arg_a0a1.HasVecRevFDerivUpdate_comp_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W] :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x : 𝕜 × X => x.1 • x.2)
      (fun x =>
        (x.1 • x.2, fun dx' dwx =>
          let' (dw,dx) := dwx
          ⟨matVecMulAdd (1:𝕜) dx' x.2 1 dw,
           dx + x.1 • dx'⟩)) := by
  sorry_proof

-- note: the statement below is not provable as it stands: `dx'` is an auto-bound universally
-- quantified variable, it should be the function's first argument `dw'`.
@[data_synth]
theorem HMul.hMul.arg_a0a1.HasVecRevFDerivUpdate_comp_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W] :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x : 𝕜 × 𝕜 => x.1 * x.2)
      (fun x =>
        (x.1 * x.2, fun dw' dw =>
          let' (dw₁, dw₂) := dw
          ⟨dw₁ + x.2 • dx',
           dw₂ + x.1 • dx'⟩)) := by
  sorry_proof


@[data_synth]
theorem HDiv.hDiv.arg_a0a1.HasVecRevFDerivUpdate_comp_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W]
    {f g : X → 𝕜} {f' g'}
    (hf : HasVecRevFDerivUpdate 𝕜 W f f') (hg : HasVecRevFDerivUpdate 𝕜 W g g')
    (hg' : ∀ x, g x ≠ 0) :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => f x / g x)
      (fun x =>
        let' (y, df') := f' x
        let' (z, dg') := g' x
        let iz := z⁻¹
        (iz • y, fun dw dx =>
          let s := ((conj z)^2)⁻¹
          let dw₁ := (-s * (conj y)) • dw
          let dw₂ := (s * (conj z)) • dw
          let dx := dg' dw₁ dx
          let dx := df' dw₂ dx
          dx)) := by
  obtain ⟨dff, hdff, adjf, hadjf, htf⟩ := hf.deriv.deriv
  obtain ⟨dgg, hdgg, adjg, hadjg, htg⟩ := hg.deriv.deriv
  have hfval := hf.val
  have hgval := hg.val
  have hfadd := hf.add_dx
  have hgadd := hg.add_dx
  have hval : ∀ x, ((g' x).1)⁻¹ • (f' x).1 = f x / g x := by
    intro x; rw [hfval, hgval, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hs : ∀ x, ((conj (g' x).1 ^ 2)⁻¹ * conj (g' x).1) = conj ((g x)⁻¹) := by
    intro x
    have hz : conj (g x) ≠ 0 := by simpa using hg' x
    rw [hgval, map_inv₀]
    field_simp [pow_two]
  have hs' : ∀ x, (-(conj (g' x).1 ^ 2)⁻¹ * conj (f' x).1)
                  = conj (-(f x * ((g x)⁻¹)^2)) := by
    intro x
    rw [hfval, hgval]
    simp only [map_neg, map_mul, map_inv₀, map_pow, neg_mul, inv_pow]
    ring
  constructor
  case val => intro x; exact hval x
  case add_dx =>
    intro x dw dx
    dsimp only
    rw [hfadd x _ ((g' x).2 _ dx), hgadd x _ dx, hfadd x _ ((g' x).2 _ 0), add_assoc]
  case deriv =>
    constructor
    case val => intro x; exact hval x
    case deriv =>
      refine ⟨fun x => ((g x)⁻¹) • dff x - (f x * ((g x)⁻¹)^2) • dgg x, fun x => ?_,
              fun x dy => adjg x ((conj (-(f x * ((g x)⁻¹)^2))) • dy)
                          + adjf x ((conj ((g x)⁻¹)) • dy), fun x => ?_, ?_⟩
      · have hinv : HasFDerivAt (fun x => (g x)⁻¹) ((-((g x)^2)⁻¹) • dgg x) x := by
          have h := HasFDerivAt.comp (𝕜:=𝕜) x ((hasDerivAt_inv (hg' x)).hasFDerivAt) (hdgg x)
          refine h.congr_fderiv (ContinuousLinearMap.ext fun dx => ?_)
          simp [smul_eq_mul, mul_comm]
        have h := (hdff x).mul hinv
        simp only [div_eq_mul_inv]
        refine h.congr_fderiv (ContinuousLinearMap.ext fun dx => ?_)
        show f x • ((-((g x)^2)⁻¹) • dgg x dx) + (g x)⁻¹ • dff x dx
             = (g x)⁻¹ • dff x dx - (f x * ((g x)⁻¹)^2) • dgg x dx
        rw [← inv_pow, smul_smul, mul_neg, neg_smul]
        abel
      · constructor
        · intro dx dy
          show ⟪(g x)⁻¹ • dff x dx - (f x * ((g x)⁻¹)^2) • dgg x dx, dy⟫[𝕜]
               = ⟪dx, adjg x ((conj (-(f x * ((g x)⁻¹)^2))) • dy)
                      + adjf x ((conj ((g x)⁻¹)) • dy)⟫[𝕜]
          rw [AdjointSpace.inner_sub_left, AdjointSpace.inner_smul_left,
            AdjointSpace.inner_smul_left, AdjointSpace.inner_add_right,
            ← (hadjf x).adjoint, ← (hadjg x).adjoint, AdjointSpace.inner_smul_right,
            AdjointSpace.inner_smul_right, map_neg]
          ring
        · have := (hadjf x).isContinuousLinearMap'
          have := (hadjg x).isContinuousLinearMap'
          fun_prop
      · intro x dy w
        dsimp only
        rw [tmul_add, htf x _ w, htg x _ w, tmul_smul, tmul_smul, hs x, hs' x,
          hfadd x _ ((g' x).2 _ 0)]
    case linear =>
      intro x
      have h1 := hf.deriv.linear x
      have h2 := hg.deriv.linear x
      dsimp only at h1 h2
      have h : (fun dw => (f' x).2 (((conj (g' x).1 ^ 2)⁻¹ * conj (g' x).1) • dw)
                            ((g' x).2 ((-(conj (g' x).1 ^ 2)⁻¹ * conj (f' x).1) • dw) 0))
             = fun dw => (g' x).2 ((-(conj (g' x).1 ^ 2)⁻¹ * conj (f' x).1) • dw) 0
                         + (f' x).2 (((conj (g' x).1 ^ 2)⁻¹ * conj (g' x).1) • dw) 0 := by
        funext dw; rw [hfadd x _ ((g' x).2 _ 0)]
      show IsContinuousLinearMap 𝕜
        (fun dw => (f' x).2 (((conj (g' x).1 ^ 2)⁻¹ * conj (g' x).1) • dw)
                     ((g' x).2 ((-(conj (g' x).1 ^ 2)⁻¹ * conj (f' x).1) • dw) 0))
      rw [h]
      fun_prop

-- The original statement below is not provable as it stands: the value `ic * y` refers to the
-- parameter `y` instead of the function's argument `x`, so `val` would force `c⁻¹ * y = x / c`
-- for all `x` and `y`. The corrected statement is proved right after it.
-- @[data_synth]
-- theorem HDiv.hDiv.arg_a0.HasVecRevFDerivUpdate_comp_rule [Module 𝕜ᵐᵒᵖ W] [Star W]
--     (y : 𝕜) :
--     HasVecRevFDerivUpdate 𝕜 W
--       (fun x : 𝕜 => x / c)
--       (fun x =>
--         let ic := c⁻¹
--         (ic * y, fun dw' dw =>
--           let dw := dw + (conj ic) • dw'
--           dw)) := by
--   sorry_proof

/-- Accumulating reverse mode derivative of division by a constant.

This is the original `HDiv.hDiv.arg_a0.HasVecRevFDerivUpdate_comp_rule` with the value `ic * y`
corrected to `ic * x`. -/
@[data_synth]
theorem HDiv.hDiv.arg_a0.HasVecRevFDerivUpdate_comp_rule [Module 𝕜ᵐᵒᵖ W] [Star W] :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x : 𝕜 => x / c)
      (fun x =>
        let ic := c⁻¹
        (ic * x, fun dw' dw =>
          let dw := dw + (conj ic) • dw'
          dw)) := by
  have hval : ∀ x : 𝕜, c⁻¹ * x = x / c := by intro x; rw [div_eq_mul_inv, mul_comm]
  constructor
  case val => intro x; exact hval x
  case add_dx =>
    intro x dw' dw
    show dw + (conj c⁻¹) • dw' = dw + (0 + (conj c⁻¹) • dw')
    rw [zero_add]
  case deriv =>
    constructor
    case val => intro x; exact hval x
    case deriv =>
      refine ⟨fun _ => c⁻¹ • ContinuousLinearMap.id 𝕜 𝕜, fun x => ?_,
              fun _ dy => (conj c⁻¹) • dy, fun x => ?_, ?_⟩
      · have h := ((hasDerivAt_id x).div_const c).hasFDerivAt
        refine h.congr_fderiv (ContinuousLinearMap.ext fun dx => ?_)
        show dx • (1 / c) = c⁻¹ • dx
        rw [smul_eq_mul, smul_eq_mul, one_div, mul_comm]
      · constructor
        · intro dx dy
          show ⟪c⁻¹ • dx, dy⟫[𝕜] = ⟪dx, (conj c⁻¹) • dy⟫[𝕜]
          rw [AdjointSpace.inner_smul_left, AdjointSpace.inner_smul_right]
        · fun_prop
      · intro x dy w
        show w ⊗ ((conj c⁻¹) • dy) = 0 + (conj c⁻¹) • (w ⊗ dy)
        rw [tmul_smul, zero_add]
    case linear =>
      intro x
      show IsContinuousLinearMap 𝕜 (fun dw' => 0 + (conj c⁻¹) • dw')
      fun_prop


@[data_synth]
theorem HInv.hInv.arg_a0.HasVecRevFDeriv_comp_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W]
    {f : X → 𝕜} {f'}
    (hf : HasVecRevFDeriv 𝕜 W f f')
    (hf' : ∀ x, f x ≠ 0) :
    HasVecRevFDeriv 𝕜 W
      (fun x => (f x)⁻¹)
      (fun x =>
        let' (y, df') := f' x
        let iy := y⁻¹
        (iy, fun dw =>
          let s := ((conj y)^2)⁻¹
          let dw := -s • dw
          let dx := df' dw
          dx)) := by
  obtain ⟨dff, hdff, adjf, hadjf, htf⟩ := hf.deriv
  have hfval := hf.val
  constructor
  case val => intro x; simp [hfval]
  case deriv =>
    refine ⟨fun x => (-(f x ^ 2)⁻¹) • dff x, fun x => ?_,
            fun x dy => adjf x ((conj (-(f x ^ 2)⁻¹)) • dy), fun x => ?_, ?_⟩
    · have h := HasFDerivAt.comp (𝕜:=𝕜) x ((hasDerivAt_inv (hf' x)).hasFDerivAt) (hdff x)
      refine h.congr_fderiv (ContinuousLinearMap.ext fun dx => ?_)
      simp [smul_eq_mul, mul_comm]
    · constructor
      · intro dx dy
        show ⟪(-(f x ^ 2)⁻¹) • dff x dx, dy⟫[𝕜] = ⟪dx, adjf x ((conj (-(f x ^ 2)⁻¹)) • dy)⟫[𝕜]
        rw [AdjointSpace.inner_smul_left, ← (hadjf x).adjoint, AdjointSpace.inner_smul_right]
      · have := (hadjf x).isContinuousLinearMap'
        fun_prop
    · intro x dy w
      dsimp only
      rw [htf x _ w, tmul_smul, hfval x]
      simp [map_neg, map_inv₀, map_pow]
  case linear =>
    intro x
    have := hf.linear x
    show IsContinuousLinearMap 𝕜 (fun dw => (f' x).2 (-((conj (f' x).1)^2)⁻¹ • dw))
    fun_prop

@[data_synth]
theorem HInv.hInv.arg_a0.HasVecRevFDerivUpdate_comp_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W]
    {f : X → 𝕜} {f'}
    (hf : HasVecRevFDerivUpdate 𝕜 W f f')
    (hf' : ∀ x, f x ≠ 0) :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => (f x)⁻¹)
      (fun x =>
        let' (y, df') := f' x
        let iy := y⁻¹
        (iy, fun dw dx =>
          let s := ((conj y)^2)⁻¹
          let dw := -s • dw
          let dx := df' dw dx
          dx)) := by
  constructor
  case val => intro x; simp [hf.val x]
  case deriv => exact HInv.hInv.arg_a0.HasVecRevFDeriv_comp_rule hf.deriv hf'
  case add_dx => intro x dy dx; exact hf.add_dx x _ dx

-- The original statements below are not provable: in reverse mode the derivative enters through
-- its adjoint, so the scalar `n • y^(n-1)` has to be conjugated - compare with
-- `HInv.hInv.arg_a0.HasVecRevFDeriv_comp_rule` above, which does conjugate. For a real scalar
-- type the two statements agree. The corrected statements are proved right after them.
-- @[data_synth]
-- theorem HPow.hPow.arg_a0.HasVecRevFDeriv_rule_nat
--     [Module 𝕜ᵐᵒᵖ W] [Star W]
--     {f : X → 𝕜} {f'}
--     (hf : HasVecRevFDeriv 𝕜 W f f') (n : ℕ) :
--     HasVecRevFDeriv 𝕜 W
--       (fun x => (f x)^n)
--       (fun x =>
--         let' (y, df') := f' x
--         (y^n,  fun dw =>
--           let dw := (n • y^(n-1)) • dw
--           let dx := df' dw
--           dx)) := by
--   sorry_proof

/-- Reverse mode derivative of natural power.

This is the original `HPow.hPow.arg_a0.HasVecRevFDeriv_rule_nat` with the scalar `n • y^(n-1)`
corrected to its conjugate `n • (conj y)^(n-1)`. -/
@[data_synth]
theorem HPow.hPow.arg_a0.HasVecRevFDeriv_rule_nat
    [Module 𝕜ᵐᵒᵖ W] [Star W]
    {f : X → 𝕜} {f'}
    (hf : HasVecRevFDeriv 𝕜 W f f') (n : ℕ) :
    HasVecRevFDeriv 𝕜 W
      (fun x => (f x)^n)
      (fun x =>
        let' (y, df') := f' x
        (y^n,  fun dw =>
          let dw := (n • (conj y)^(n-1)) • dw
          let dx := df' dw
          dx)) := by
  obtain ⟨dff, hdff, adjf, hadjf, htf⟩ := hf.deriv
  have hfval := hf.val
  constructor
  case val => intro x; simp [hfval]
  case deriv =>
    refine ⟨fun x => (n • f x ^ (n-1)) • dff x, fun x => (hdff x).pow n,
            fun x dy => adjf x ((conj ((n:𝕜) • f x ^ (n-1))) • dy), fun x => ?_, ?_⟩
    · constructor
      · intro dx dy
        show ⟪(n • f x ^ (n-1)) • dff x dx, dy⟫[𝕜]
             = ⟪dx, adjf x ((conj ((n:𝕜) • f x ^ (n-1))) • dy)⟫[𝕜]
        rw [AdjointSpace.inner_smul_left, ← (hadjf x).adjoint, AdjointSpace.inner_smul_right,
          Nat.cast_smul_eq_nsmul]
      · fun_prop
    · intro x dy w
      dsimp only
      rw [htf x _ w, tmul_smul, hfval x]
      simp [map_pow, nsmul_eq_mul]
  case linear =>
    intro x
    have := hf.linear x
    show IsContinuousLinearMap 𝕜 (fun dw => (f' x).2 ((n • (conj (f' x).1)^(n-1)) • dw))
    fun_prop

-- @[data_synth]
-- theorem HPow.hPow.arg_a0.HasVecRevFDerivUpdate_rule_nat
--     [Module 𝕜ᵐᵒᵖ W] [Star W]
--     {f : X → 𝕜} {f'}
--     (hf : HasVecRevFDerivUpdate 𝕜 W f f') (n : ℕ) :
--     HasVecRevFDerivUpdate 𝕜 W
--       (fun x => (f x)^n)
--       (fun x =>
--         let' (y, df') := f' x
--         (y^n,  fun dw dx =>
--           let dw := (n • y^(n-1)) • dw
--           let dx := df' dw dx
--           dx)) := by

/-- Accumulating reverse mode derivative of natural power.

This is the original `HPow.hPow.arg_a0.HasVecRevFDerivUpdate_rule_nat` with the scalar
`n • y^(n-1)` corrected to its conjugate `n • (conj y)^(n-1)`. -/
@[data_synth]
theorem HPow.hPow.arg_a0.HasVecRevFDerivUpdate_rule_nat
    [Module 𝕜ᵐᵒᵖ W] [Star W]
    {f : X → 𝕜} {f'}
    (hf : HasVecRevFDerivUpdate 𝕜 W f f') (n : ℕ) :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => (f x)^n)
      (fun x =>
        let' (y, df') := f' x
        (y^n,  fun dw dx =>
          let dw := (n • (conj y)^(n-1)) • dw
          let dx := df' dw dx
          dx)) := by
  constructor
  case val => intro x; simp [hf.val x]
  case deriv => exact HPow.hPow.arg_a0.HasVecRevFDeriv_rule_nat hf.deriv n
  case add_dx => intro x dy dx; exact hf.add_dx x _ dx


set_option linter.unusedVariables false in
@[data_synth]
theorem SciLean.IndexType.sum.arg_f.HasVecRevFDeriv_rule
    {I : Type*} {nI} [IndexType I nI] [Fold I] [Fold I]
    {f : X → I → Y} {f' : I → _}
    (hf : ∀ i, HasVecRevFDerivUpdate 𝕜 W (f · i) (f' i)) :
    HasVecRevFDeriv 𝕜 W
      (fun x => ∑ᴵ i, f x i)
      (fun x =>
        (∑ᴵ i, f x i,
         fun dy =>
           IndexType.fold .full (init:=(0 : W⊗X)) fun i dx =>
             let dx := (f' i x).2 dy dx
             dx)) := by
  -- the accumulating pullbacks only add to the accumulator, so the fold is just the sum
  have hfold : ∀ x (dy : W⊗Y),
      (IndexType.fold .full (init:=(0 : W⊗X)) fun (i : I) (dx : W⊗X) => (f' i x).2 dy dx)
      =
      ∑ i : I, (f' i x).2 dy 0 := by
    intro x dy
    rw [show (fun (i : I) (dx : W⊗X) => (f' i x).2 dy dx)
           = (fun (i : I) (dx : W⊗X) => dx + (f' i x).2 dy 0) from
          by funext i dx; rw [(hf i).add_dx x dy dx]]
    show IndexType.sum (fun i => (f' i x).2 dy 0) = _
    rw [IndexType.sum_eq_finset_sum]
  choose df hdf adj hadj htmul using fun i => (hf i).deriv.deriv
  constructor
  case val => intro x; rfl
  case deriv =>
    refine ⟨fun x => ∑ i : I, df i x, ?_, fun x dy => ∑ i : I, adj i x dy, ?_, ?_⟩
    · intro x
      simp only [IndexType.sum_eq_finset_sum]
      exact HasFDerivAt.fun_sum (fun i _ => hdf i x)
    · intro x
      constructor
      case adjoint =>
        intro dx dy
        rw [sum_apply, AdjointSpace.sum_inner, AdjointSpace.inner_sum]
        exact Finset.sum_congr rfl fun i _ => (hadj i x).adjoint dx dy
      case is_linear => fun_prop
    · intro x dy w
      show w ⊗ (∑ i : I, adj i x dy)
         = IndexType.fold .full (init:=(0 : W⊗X)) fun (i : I) (dx : W⊗X) => (f' i x).2 (w ⊗ dy) dx
      have hlin : w ⊗ (∑ i : I, adj i x dy) = ∑ i : I, (w ⊗ adj i x dy : W⊗X) :=
        map_sum (IsLinearMap.mk' _ (tmul.arg_x.IsLinearMap_rule (R:=𝕜) (YX:=W⊗X) w))
          (fun i => adj i x dy) Finset.univ
      rw [hfold x (w ⊗ dy), hlin]
      exact Finset.sum_congr rfl fun i _ => htmul i x dy w
  case linear =>
    intro x
    have h : ∀ i : I, IsContinuousLinearMap 𝕜 (fun dy : W⊗Y => (f' i x).2 dy 0) :=
      fun i => (hf i).deriv.linear x
    have he : (fun dy : W⊗Y =>
          IndexType.fold .full (init:=(0 : W⊗X)) fun (i : I) (dx : W⊗X) => (f' i x).2 dy dx)
        = ⇑(∑ i : I, ContinuousLinearMap.mk' 𝕜 (fun dy : W⊗Y => (f' i x).2 dy 0) (h i)) := by
      funext dy; rw [hfold x dy, sum_apply]; rfl
    rw [he]
    fun_prop

set_option linter.unusedVariables false in
@[data_synth]
theorem SciLean.IndexType.sum.arg_f.HasVecRevFDerivUpdate_rule
    {I : Type*} {nI} [IndexType I nI] [Fold I] [Fold I]
    {f : X → I → Y} {f' : I → _}
    (hf : ∀ i, HasVecRevFDerivUpdate 𝕜 W (f · i) (f' i)) :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => ∑ᴵ i, f x i)
      (fun x =>
        (∑ᴵ i, f x i,
         fun dy dx =>
           IndexType.fold .full (init:=dx) fun i dx =>
             let dx := (f' i x).2 dy dx
             dx)) := by
  constructor
  case val => intro x; rfl
  case deriv => exact SciLean.IndexType.sum.arg_f.HasVecRevFDeriv_rule hf
  case add_dx =>
    intro x dy dx
    show IndexType.fold .full (init:=dx) (fun (i : I) (dx : W⊗X) => (f' i x).2 dy dx)
       = dx + IndexType.fold .full (init:=(0 : W⊗X)) (fun (i : I) (dx : W⊗X) => (f' i x).2 dy dx)
    rw [show (fun (i : I) (dx : W⊗X) => (f' i x).2 dy dx)
           = (fun (i : I) (dx : W⊗X) => dx + (f' i x).2 dy 0) from
          by funext i dx; rw [(hf i).add_dx x dy dx]]
    rw [IndexType.fold_add_eq_add_sum, IndexType.fold_add_eq_add_sum, zero_add]


section OverReals

variable
  {𝕜 : Type*} [RealScalar 𝕜]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
  {Z : Type*} [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace 𝕜 W]
  {WX : Type*} [NormedAddCommGroup WX] [AdjointSpace 𝕜 WX]
  {WY : Type*} [NormedAddCommGroup WY] [AdjointSpace 𝕜 WY]
  {WZ : Type*} [NormedAddCommGroup WZ] [AdjointSpace 𝕜 WZ]
  [TensorProductType 𝕜 W X WX] [TensorProductGetYX 𝕜 W X WX]
  [TensorProductType 𝕜 W Y WY] [TensorProductGetYX 𝕜 W Y WY]
  [TensorProductType 𝕜 W Z WZ] [TensorProductGetYX 𝕜 W Z WZ]


open ComplexConjugate TensorProductType

set_default_scalar 𝕜

@[data_synth]
theorem Inner.inner.arg_a0a1.HasVecRevFDeriv_simple_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W] :
    HasVecRevFDeriv 𝕜 W
      (fun x : X×X => ⟪x.1, x.2⟫[𝕜])
      (fun x =>
        (⟪x.1, x.2⟫[𝕜], fun dw =>
          ⟨dw ⊗ x.2, dw ⊗ x.1⟩)) := by
  sorry_proof

@[data_synth]
theorem Inner.inner.arg_a0a1.HasVecRevFDerivUpdate_simple_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W] :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x : X×X => ⟪x.1, x.2⟫[𝕜])
      (fun x =>
        (⟪x.1, x.2⟫[𝕜], fun dw dx =>
          let' (dx₁,dx₂) := dx
          ⟨tmulAdd (1:𝕜) dw x.2 dx₁, tmulAdd (1:𝕜) dw x.1 dx₂⟩)) := by
  constructor
  case val => intro x; rfl
  case deriv => exact Inner.inner.arg_a0a1.HasVecRevFDeriv_simple_rule
  case add_dx =>
    intro x dy dx
    obtain ⟨dx₁,dx₂⟩ := dx
    show (⟨tmulAdd 1 dy x.2 dx₁, tmulAdd 1 dy x.1 dx₂⟩ : ProdMatrixRow _ _)
         = ⟨dx₁ + tmulAdd 1 dy x.2 0, dx₂ + tmulAdd 1 dy x.1 0⟩
    simp [tmulAdd_spec, add_comm]

@[data_synth]
theorem Norm2.norm2.arg_a0.HasVecRevFDerivUpdate_simple_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W] :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x : X => ‖x‖₂²[𝕜])
      (fun x =>
        (‖x‖₂²[𝕜], fun dw' dw =>
          let dw := tmulAdd (2:𝕜) dw' x dw
          dw)) := by
  sorry_proof

@[data_synth]
theorem SciLean.norm₂.arg_x.HasVecRevFDeriv_comp_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W]
    (f : X → Y) {f'} (hf : HasVecRevFDeriv 𝕜 W f f') (hf' : ∀ x, f x ≠ 0) :
    HasVecRevFDeriv 𝕜 W (fun x => ‖f x‖₂[𝕜])
      (fun x =>
        let' (y, df') := f' x
        let yn := ‖y‖₂[𝕜]
        (yn, fun dw : W =>
          let dir := yn⁻¹ • y
          let dx := df' (dw ⊗ dir)
          dx)) := by
  sorry_proof

end OverReals
