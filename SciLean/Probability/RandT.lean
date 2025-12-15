import SciLean.Probability.Rand

namespace SciLean

universe v

/-- Monad transformer for computations guided by `StdGen` randomness.

Note: `StdGen : Type` lives in universe 0, so this transformer is restricted to
monads over `Type` (universe 0).
-/
abbrev RandT (m : Type → Type v) := StateT StdGen m

/-- A pure random computation (generator threaded explicitly). -/
abbrev RandG := RandT Id

namespace RandT

@[inline] def eval [Monad m] (x : RandT m α) (g : StdGen) : m α := do
  let (a, _) ← x.run g
  return a

@[inline] def exec [Monad m] (x : RandT m α) (g : StdGen) : m StdGen := do
  let (_, g) ← x.run g
  return g

/-- Run a random computation in `IO` using Lean's global `StdGen` reference. -/
@[inline] def runIO (x : RandT IO α) : IO α := do
  let g ← IO.stdGenRef.get
  let (a, g) ← x.run g
  IO.stdGenRef.set g
  return a

end RandT

instance : MonadLift (StateM StdGen) Rand where
  monadLift x := { spec := default, rand := x }

instance [MonadLift m n] : MonadLiftT (RandT m) (RandT n) where
  monadLift x := fun s => monadLift (x.run s)

end SciLean
