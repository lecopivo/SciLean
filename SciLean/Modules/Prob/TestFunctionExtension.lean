import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace SciLean.Prob


-- Extend `F` functional on test function to to a Y-valued functional.
-- not every `f` can have such extension
-- extension is valid if does not depend on the appxosimation of `f` by test functions
noncomputable
opaque testFunctionExtension
  {X} -- X needs a predicat that it has a notion of test functions
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (F : (X → ℝ) → ℝ) (f : X → Y) : Y := sorry


/-- Extension on simple test function is equal to the original function. -/
theorem testFunctionExtension_test_function
    {X} -- X needs a predicat that it has a notion of test functions
    {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : (X → ℝ) → ℝ) (φ : X → ℝ) (y : Y) :
    testFunctionExtension F (fun x => φ x • y)
    =
    F φ • y := sorry


/-- If `F` `G` agree on simple test functions then extension of `F` at `f` is equal to `G f`.

TODO: add requirement that `F` has extension at `f` and constrain `φ` to be test funcitons. -/
theorem testFunctionExtension_ext
    {X} -- X needs a predicat that it has a notion of test functions
    {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : (X → ℝ) → ℝ) (G : (X → Y) → Y) (f : X → Y)
    (h : ∀ (φ : X → ℝ) (y : Y), F φ • y = G (φ · • y)) :
    testFunctionExtension F f
    =
    G f := sorry
