import Lean
namespace SciLean

/--
Gadget structure providing a term that is either `a` or `b`.

Sometimes you know that a certain term has multiple alternative forms and you do not want to pick one or the other. The decision which version should
-/
structure Alternatives {α} (a b : α) where
  eq : a = b

set_option linter.unusedVariables false in
@[irreducible]
def Alternatives.choose {α} (a b : α) (ap : Alternatives a b) : α := a

theorem Alternatives.pick_fst {α} {a b : α} (ap : Alternatives a b)
  : ap.choose = a := by unfold Alternatives.choose; rfl

theorem Alternatives.pick_snd {α} {a b : α} (ap : Alternatives a b)
  : ap.choose = b := by unfold Alternatives.choose; rw [ap.eq]

/-- Term equal either to `x` or `y`.

Pick `x` by calling tactic `alternatives_fst` or `y` by calling `alternatives_snd`

Example:

```
alternatives
  fst: 8
  snd: 2^3
  by native_decide
```

This is a term equal to `8` or `2^3`, each form might be usefull in different scenarios.
-/
macro " alternatives " linebreak " fst: " a:term linebreak " snd: " b:term  linebreak " by " proof:tacticSeq : term =>
  `(Alternatives.choose $a $b (Alternatives.mk (by $proof)))

macro " alternatives " linebreak " fst: " a:term linebreak " snd: " b:term  linebreak " by' " proof:term : term =>
  `(Alternatives.choose $a $b (Alternatives.mk $proof))


macro " alternatives_fst " : tactic => `(tactic| simp (config := {zeta := false}) only [Alternatives.pick_fst])
macro " alternatives_snd " : tactic => `(tactic| simp (config := {zeta := false}) only [Alternatives.pick_snd])
macro " alternatives_fst " : conv => `(conv| simp (config := {zeta := false}) only [Alternatives.pick_fst])
macro " alternatives_snd " : conv => `(conv| simp (config := {zeta := false}) only [Alternatives.pick_snd])


@[app_unexpander Alternatives.choose] def unexpandAlternativecChoose : Lean.PrettyPrinter.Unexpander
  | `($(_) $a $b $_) =>
    `(alternatives
       fst: $a
       snd: $b
       by' _)
  | `($(_) $a $b $_ $x) =>
    `(alternatives
       fst: $a $x
       snd: $b $x
       by' _)
  | `($(_) $a $b $_ $x $y) =>
    `(alternatives
       fst: $a $x $y
       snd: $b $x $y
       by' _)
  | _  => throw ()


variable (a b : Nat) (h : a = b)



/--
info:  alternatives fst: fun x =>
  let y := x + x + x + x;
  y + y snd:
  fun x =>
  let y := x + x + x + x;
  let y := x + x + x + x;
  x + x + x + x by'
  _ : Nat → Nat
-/
#guard_msgs in
#check
  alternatives
    fst:
      λ x : Nat =>
        let y := x + x + x + x
        y + y
    snd:
      λ x : Nat =>
        let y := x + x + x + x
        let y := x + x + x + x
        x + x + x + x
    by sorry
