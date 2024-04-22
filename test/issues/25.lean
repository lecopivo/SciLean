import SciLean

open SciLean

variable
  (K : Type _) [RCLike K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]

example
  (f : Y → Z) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revDerivUpdate K (fun x : X => f (g x))
    =
    fun x =>
      let ydg := revDerivUpdate K g x
      let zdf := revDerivUpdate K (fun x' => f (ydg.1 + semiAdjoint K (ydg.2 · 0) (x' - x))) x
      zdf :=
by
  unfold revDerivUpdate
  funext _;
  conv => lhs; fun_trans
  conv =>
    rhs
    enter [ydg]
    fun_trans -- this breaks fun_trans :( not sure why
  simp[revDeriv]
  fun_trans
