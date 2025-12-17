import SciLean

open SciLean

variable
  (K : Type _) [RCLike K]
  {W : Type _} [NormedAddCommGroup W] [AdjointSpace K W]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [AdjointSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [AdjointSpace K Z]


-- old test no longer valid
-- example
--   (f : Y → Z) (g : X → Y)
--   (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
--   : revCDerivUpdate K (fun x : X => f (g x))
--     =
--     fun x =>
--       let ydg := revCDerivUpdate K g x
--       let zdf := revCDerivUpdate K (fun x' => f (ydg.1 + semiAdjoint K (ydg.2 · 0) (x' - x))) x
--       zdf :=
-- by
--   unfold revCDerivUpdate
--   funext _;
--   conv => lhs; fun_trans
--   conv =>
--     rhs
--     enter [ydg]
--     fun_trans -- this breaks fun_trans :( not sure why
--   simp[revCDeriv]
--   fun_trans
