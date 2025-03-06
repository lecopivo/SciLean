import SciLean.Analysis.Calculus.HasFDeriv
import SciLean.Analysis.Calculus.FwdFDeriv

namespace SciLean


variable
  {K : Type*} [RCLike K]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace K Z]

variable (K) in
@[data_synth out f' in f]
structure HasFwdFDeriv (f : X → Y) (f' : X → X → Y×Y) where
  val : ∀ x dx, (f' x dx).1 = f x
  deriv : ∃ df : X → X →L[K] Y,
      (∀ x, HasFDerivAt f (df x) x)
      ∧
      (∀ x dx, df x dx = (f' x dx).2)


----------------------------------------------------------------------------------------------------
-- API for constructing and deconstructing HasFwdFDeriv -----------------------------------
----------------------------------------------------------------------------------------------------

theorem hasFwdFDeriv_from_hasFDerivAt {f : X → Y}
    {df : X → X →L[K] Y} (deriv : ∀ x, HasFDerivAt (𝕜:=K) f (df x) x)
    {f' : X → X → Y×Y} (simp : ∀ x dx, f' x dx = (f x, df x dx)) :
    HasFwdFDeriv K f f' := by
  constructor
  case val =>
    simp[simp]
  case deriv =>
    apply Exists.intro df
    simp_all


set_option linter.unusedVariables false in
-- @[to_data_synth_simproc] -- this attribute should automatically generate the following simproc
theorem fwdFDeriv_from_hasFwdFDeriv
  {f : X → Y} {f'} (hf : HasFwdFDeriv K f f') :
  fwdFDeriv K f = f' := sorry_proof

simproc_decl fwdFDeriv_simproc (fwdFDeriv _ _) :=
  mkDataSynthSimproc `revFDeriv_simproc ``fwdFDeriv_from_hasFwdFDeriv



----------------------------------------------------------------------------------------------------
-- Lambda Theorems ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[data_synth]
theorem id_rule : HasFwdFDeriv K (id : X → X) (λ x dx => (x, dx)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv =>
    intro x
    apply hasFDerivAt_id
  case simp => simp

theorem const_rule (c : Y) : HasFwdFDeriv K (Function.const X c) (λ _ _ => (c, 0)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv =>
    intro x
    apply hasFDerivAt_const
  case simp => simp

theorem comp_rule {g : X → Y} {f : Y → Z} {g' : X → X → Y×Y} {f' : Y → Y → Z×Z}
    (hf : HasFwdFDeriv K f f') (hg : HasFwdFDeriv K g g') :
    HasFwdFDeriv K
      (fun x => f (g x))
      (fun x dx =>
        let' (y, dy) := g' x dx;
        let' (z, dz) := f' y dy;
        (z, dz)) := by
  obtain ⟨hfv,df,hfd,hfd'⟩ := hf
  obtain ⟨hgv,dg,hgd,hgd'⟩ := hg
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv =>
    intro x
    exact (hfd (g x)).comp x (hgd x)
  case simp =>
    intros
    simp_all

theorem let_rule {g : X → Y} {f : Y → X → Z} {f' g'}
    (hg : HasFwdFDeriv K g g') (hf : HasFwdFDeriv K (↿f) f') :
    HasFwdFDeriv K
      (fun x =>
        let y := g x
        f y x)
      (fun x dx =>
        let' (y, dy) := g' x dx
        let' (z, dz) := f' (y,x) (dy,dx)
        (z, dz)) := by
  obtain ⟨hfv,df,hfd,hfd'⟩ := hf
  obtain ⟨hgv,dg,hgd,hgd'⟩ := hg
  have hg' : HasFwdFDeriv K
    (fun x => (g x, x))
    (fun x dx => let' (y,dy) := g' x dx; ((y,x),(dy,dx))) := sorry_proof
  obtain ⟨hgv',dg',hgd',hgd''⟩ := hg'
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv =>
    intro x
    exact (hfd (g x,x)).comp x (f:=fun x => (g x, x)) (hgd' x)
  case simp =>
    intros
    simp_all
    rfl

set_option linter.unusedVariables false in
theorem pi_rule {I : Type*} [IndexType I]
    {f : X → I → Y} {f' : I → _} (hf : ∀ i, HasFwdFDeriv K (f · i) (f' i)) :
    HasFwdFDeriv K f
      (fun x dx =>
        Equiv.arrowProdEquivProdArrow _ _ _ (fun i => f' i x dx)) := by

  sorry_proof
  -- apply hasFwdFDeriv_from_hasFDerivAt
  -- case deriv =>
  --   intro x

  --   apply hasFDerivAt_pi
  --   intro i
  --   apply (hf i).deriv.1

open Lean Meta
#eval show MetaM Unit from do
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFwdFDeriv,``const_rule⟩, .const⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFwdFDeriv, ``comp_rule⟩, .comp
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f)
      (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFwdFDeriv,``let_rule⟩, .letE
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f)
      (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFwdFDeriv,``pi_rule⟩, .pi
      (← getConstArgId ``pi_rule `f) (← getConstArgId ``pi_rule `hf)⟩
  --  Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFwdFDeriv,``proj_rule⟩, .proj
  --     (← getConstArgId ``proj_rule `f) (← getConstArgId ``proj_rule `g)
  --     (← getConstArgId ``proj_rule `p₁) (← getConstArgId ``proj_rule `p₂)
  --     (← getConstArgId ``proj_rule `q) (← getConstArgId ``proj_rule `hg)⟩
