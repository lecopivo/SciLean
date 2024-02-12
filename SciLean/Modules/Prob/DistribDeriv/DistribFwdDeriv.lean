import SciLean.Modules.Prob.DistribDeriv.DistribDeriv

namespace SciLean.Prob



variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [MeasurableSpace Z]


structure FDistribution (X : Type _) where
  val  : Distribution X
  dval : Distribution X

-- instance : FunLike (FDistribution X) (X → ℝ) (fun _ => ℝ×ℝ) where
--   coe := fun f φ => (f.val φ, f.dval φ)
--   coe_injective' := sorry

instance : FunLike (FDistribution X) (X → ℝ×ℝ) (fun _ => ℝ×ℝ) where
  coe := fun f φ => (f.val (fun x => (φ x).1), (f.dval (fun x => (φ x).1)) + (f.val (fun x => (φ x).2)))
  coe_injective' := sorry


@[simp]
theorem FDistribution_apply (val dval : Distribution X) (φ : X → ℝ×ℝ) :
    FDistribution.mk val dval φ = (val (fun x => (φ x).1), (dval (fun x => (φ x).1)) + (val (fun x => (φ x).2))) := by rfl


instance : Monad FDistribution where
  pure := fun x => { val := pure x, dval := 0 }
  bind := fun x f =>
    ⟨(Bind.bind x.val (fun x' => (f x').val)),
       Bind.bind x.dval (fun x' => (f x').val)
       +
       Bind.bind x.val (fun x' => (f x').dval)⟩


----------------------------------------------------------------------------------------------------

noncomputable
def distribFwdDeriv
    (f : X → Distribution Y) (x dx : X) : FDistribution Y :=
  ⟨f x, distribDeriv f x dx⟩


@[simp]
theorem distribFwdDeriv_const (a : Distribution α) :
    distribFwdDeriv (fun _ : X => a)
    =
    fun w _dw => ⟨a,0⟩ := by unfold distribFwdDeriv; simp



-- WARNING: uses `distribDeriv_comp` axiom
theorem distribFwdDeriv_comp (f : Y → Distribution Z) (g : X → Y) (x dx : X) (φ : Z → ℝ×ℝ)
    (hf : DistribDifferentiable f) (hg : DifferentiableAt ℝ g x) :
    distribFwdDeriv (fun x : X => (f (g x))) x dx φ
    =
    let ydy := fwdFDeriv ℝ g x dx
    distribFwdDeriv f ydy.1 ydy.2 φ := by

  simp (disch:=assumption) [distribFwdDeriv,fwdFDeriv, distribDeriv_comp]


-- WARNING: uses `Rand.bind.arg_xf.distribDeriv_rule`
theorem FDistribution.bind.arg_xf.distribFwdDeriv_rule
    (g : X → Distribution Y) (f : X → Y → Distribution Z) (φ : Z → ℝ×ℝ) (x dx : X)
    (hg : DistribDifferentiable g) (hf : DistribDifferentiable (fun (x,y) => f x y)) :
    distribFwdDeriv (fun x' => Bind.bind (g x') (f x')) x dx φ
    =
    (distribFwdDeriv g x dx) (fun y => distribFwdDeriv (f · y) x dx φ)  := by

  simp (disch:=assumption) [distribFwdDeriv, fwdFDeriv, Rand.bind.arg_xf.distribDeriv_rule]

  constructor

  . rfl
  . simp[add_assoc]
    sorry -- DistribDifferentiable should have linearity in φ




----------------------------------------------------------------------------------------------------


@[simp ↓]
theorem ite.arg_te.distribFwdDeriv_rule {c} [Decidable c] (t e : X → Distribution Y) (φ : Y → ℝ×ℝ) :
    distribFwdDeriv (fun x => if c then t x else e x) x dx φ
    =
    if c then distribFwdDeriv t x dx φ else distribFwdDeriv e x dx φ := by

  if h : c then simp[h] else simp[h]
