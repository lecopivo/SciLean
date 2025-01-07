import SciLean
import SciLean.Examples.GMM.Util
import SciLean.Examples.GMM.ObjectiveDirect

open SciLean.Examples.GMM

open SciLean

def main : IO Unit := do

  let data ← loadData 10 10 1000

  let start ← IO.monoNanosNow
  let r ← (Rand.uniform (Set.Ioo 0.0 1.0)).get -- to prevent common subexpression elimination
  let l := gmmObjective data.α data.μ data.q data.l data.x (data.γ + r - r) data.m -- data.x data.α data.μ data.q data.l
  -- let l' := objectiveFun 10 (data.m + r - r) data.x |>.f  (data.α,data.μ,data.q,data.l)
  -- let g := (objectiveFun 10 (data.m + r - r) data.x |>.f'  (data.α,data.μ,data.q,data.l)).2 1
  let stop ← IO.monoNanosNow

  let t := (start-stop).toFloat * 1e-6
  IO.println s!"Evaluating objective took {t}ms"
  IO.println s!"Loss  := {l}"
  -- IO.println s!"Loss' := {l'}"
  -- IO.println s!"grad := {g}"
