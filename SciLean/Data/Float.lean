import Mathlib.Order.Notation

namespace Float


/-- The gamma function. -/
@[extern "scilean_float_tgamma"]
opaque tgamma (x : Float) : Float

/-- The natural logarithm of the absolute value of the gamma function. -/
@[extern "scilean_float_lgamma"]
opaque lgamma (x : Float) : Float

partial def npowRec (x : Float) (n : Nat) : Float :=
  go x n 1.0
where
  go (x : Float) (n : Nat) (r : Float) : Float :=
    match n with
    | 0 => 1
    | 1 => x*r
    | _ =>
      if n % 2 == 1 then
        go (x*x) (n/2) (r*x)
      else
        go (x*x) (n/2) r

@[inline]
partial def npow (x : Float) (n : Nat) : Float :=
  match n with
  | 0 => 1.0
  | 1 => x
  | 2 => x*x
  | 3 => x*x*x
  | 4 => (x*x)*(x*x)
  | _ => x.npowRec n

@[inline]
partial def zpow (x : Float) (n : Int) : Float :=
  if 0 ≤ n then
    x.npow n.toNat
  else
    (1.0/x).npow (-n).toNat


def inf := 1.0/0.0
def ninf := -Float.inf
instance : Top Float := ⟨Float.inf⟩
instance : Bot Float := ⟨Float.ninf⟩
