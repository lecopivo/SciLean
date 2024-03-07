import SciLean.Core.Defs
import Mathlib.Init.Function

namespace SciLean

-- attributes
-- fun_trans_def - define a new function transformation
-- fun_trans - user facing attribute to define a rule for primitive function, most likely a simp rule
-- fun_trans_rule - core rule to deal with lambda calculus - I, K, S, B, C, let, forall, proj, prod

-- fun_prop_def - define a new function proposition
-- fun_prop - user facing attribute to define a rule for primitive function, aesop rule or type class inference
-- fun_prop_rule - core rule to deal with lambda claculus



-- Transformations
#check ``differential
#check ``tangentMap

#check ``adjoint

#check ``adjointDifferential
#check ``reverseDifferential

#check ``Function.invFun

-- Predicates
#check ``IsSmooth
#check ``IsLin
#check ``HasAdjoint
#check ``HasAdjDiff




-- def Array.swap (a : Array α) (i j : Fin a.size) : Array α := Id.run do
--   let mut a := a
--   let tmp := a[i]
--   a := a.set i a[j]
--   a := a.set j tmp
--   a
