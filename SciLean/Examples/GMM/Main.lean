import SciLean
import SciLean.Examples.GMM.Util
import SciLean.Examples.GMM.ObjectiveDirect

open SciLean

open SciLean.Examples

def main : IO Unit := do

  let data ← GMM.loadData 10 10 1000

  let start ← IO.monoNanosNow
  let l := gmmObjective data.α data.μ data.q data.l data.x data.γ data.m
  -- let l' := objectiveFun 10 (data.m + r - r) data.x |>.f  (data.α,data.μ,data.q,data.l)
  -- let g := (objectiveFun 10 (data.m + r - r) data.x |>.f'  (data.α,data.μ,data.q,data.l)).2 1
  let stop ← IO.monoNanosNow

  let t := (stop-start).toFloat * 1e-6
  IO.println s!"Evaluating objective took {t}ms"
  IO.println s!"Loss  := {l}"
  -- IO.println s!"Loss' := {l'}"
  -- IO.println s!"grad := {g}"
