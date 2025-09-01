
/-- P(n) = x^n * exp (-x) / n! -/
def randNatPoisson (x : ℝ) : Rand ℕ := sorry


/-- DP(n) = (n * x^(n-1) - x^n) * exp (-x) / n! -/
def drandNatPoisson (x : ℝ) : DRand ℕ := sorry


def flip (x : ℝ) : Rand Bool := sorry
def dflip : DRand Bool := sorry


@[simp]
theorem randDeriv_poisson : randDeriv randNatPoisson = fun x dx => dx • drandNatPoisson x := sorry


@[simp]
theorem randDeriv_ite {c} [Decidable c]
  (t f : W → Rand α) (ht : RandDifferentiable t) (hf : RandDifferentiable f)
  : randDeriv (fun w => if c then t w else f w) 
    = 
    fun w dw => if c then randDeriv t w dw else randDeriv f w dw := sorry

@[simp]
theorem randFwdDeriv_ite {c} [dec : Decidable c]
  (t f : W → Rand α) (ht : RandDifferentiable t) (hf : RandDifferentiable f)
  : randFwdDeriv (fun w => if c then t w else f w) 
    = 
    fun w dw => if c then randFwdDeriv t w dw else randFwdDeriv f w dw := by
  
  unfold randFwdDeriv; aesop
  



@[simp]
theorem randDeriv_flip : randDeriv flip = fun x dx => dx•dflip := sorry

noncomputable
def draw (x : ℝ): Rand ℝ :=
  let b ~ (flip x)
  if b then
    (0 : ℝ)
  else
    (- x / (2:ℝ))

macro "ad" : conv => `(conv| simp (disch:=sorry) only [randFwdDeriv_bind,randDeriv_pure, randDeriv_bind,randDeriv_poisson,randDeriv_const, randDeriv_flip,randDeriv_ite])

set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.simp.rewrite true in
#check randFwdDeriv draw
  rewrite_by
  unfold draw
  ad
  simp (disch:=sorry) only [randDeriv_pure] 
  
