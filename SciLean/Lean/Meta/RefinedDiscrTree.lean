import Lean
import Mathlib.Lean.Meta.RefinedDiscrTree.Lookup

namespace Lean.Meta.RefinedDiscrTree

/--
A temporary replacement for the missing `getMatchWithScoreWithExtra`.
Matches `e` and all its prefixes (peeling off arguments) against the tree.
-/
def getMatchWithExtra (d : RefinedDiscrTree α) (e : Expr) (unify : Bool) :
    MetaM (Array (Array α × (Nat × Nat))) := do
  let mut results := #[]
  let mut e' := e
  let mut numExtraArgs := 0
  while true do
    let (matchResult, _) ← d.getMatch e' unify (matchRootStar := true)
    if let .ok matchResult := matchResult then
      -- MatchResult.elts is TreeMap Nat (Array (Array α))
      for (score, arrs) in matchResult.elts do
        for thms in arrs do
          results := results.push (thms, (score, numExtraArgs))
    if e'.isApp then
      e' := e'.appFn!
      numExtraArgs := numExtraArgs + 1
    else
      break
  return results

end Lean.Meta.RefinedDiscrTree
