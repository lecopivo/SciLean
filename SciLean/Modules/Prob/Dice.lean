import Probly.Basic
import Probly.RewriteBy

open ENNReal BigOperators Finset

namespace Probly

def countScore (x : Rand ℕ) (throws maxVal : ℕ) : IO (Array ℕ) := do
  let mut s : Array ℕ := .mkArray maxVal 0
  for _ in [0:throws] do
    let n ← x.get
    let n := n-1
    s := s.set! n (s[n]!+1)
  return s


def throwDice1 : Rand ℕ :=
  let n ~ (randNat 1 6)
  let m ~ (randNat 1 6)
  n + m

/-
fun y ↦
  1/6 * ∑ n in Icc 1 6,
    1/6 * ∑ n_1 in Icc 1 6,
      if n + n_1 = y then 1 else 0
-/
#check throwDice1.pdf' .count
  rewrite_by
    simp[throwDice1,-Finset.sum_boole]


-- quite slow when interpreted but it is reasonably fast when compiled
/-
exmaple result:
  #[0, 2, 3, 8, 14, 15, 15, 9, 13, 13, 6, 2]
-/
#eval countScore throwDice1 100 12

def throwDice2 : Rand ℕ :=
  let n ~ (randNat 1 6)
  if n ≠ 6 then
    n
  else
    let m ~ (randNat 1 6)
    n + m

/-
fun y ↦
    1/6 * ∑ n in Icc 1 6,
      if n = 6 then
        1/6 * ∑ n_1 in Icc 1 6, if n + n_1 = y then 1 else 0
      else
        if n = y then 1 else 0
-/
#check throwDice2.pdf' .count
  rewrite_by
    simp[throwDice1,-Finset.sum_boole]

/-
example result:
  #[16, 19, 23, 15, 18, 0, 2, 1, 2, 1, 1, 2]
-/
#eval countScore throwDice2 100 12
