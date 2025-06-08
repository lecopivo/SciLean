import SciLean.Tactic.MetaFunction.Decl
import SciLean.Tactic.MetaFunction.Def
import SciLean.Meta.Notation.Let'

-- Mathlib.Topology.Instances.Real.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Lean.Meta.RefinedDiscrTree
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add

open SciLean

section NaiveBounds

open Set

meta_fun_decl naiveBoundOn (f : ℤ → ℤ) (s : Set ℤ) : ℤ
satisfying
  (∀ x ∈ s, |f x| ≤ naiveBoundOn)

meta_fun_def naiveBoundsOnIdentity (a b : ℤ) :
  naiveBoundOn (fun x => x) (Icc a b) := max |a| |b|
satisfied_by
  constructor; rintro x ⟨ha,hb⟩; simp_all; sorry_proof

meta_fun_def naiveBoundsOnConst (c a b : ℤ) :
  naiveBoundOn (fun _ => id c) (Icc a b) := |c|
satisfied_by
  constructor; rintro x _; simp_all

meta_fun_def naiveBoundsOnAdd (f g : ℤ → ℤ) (a b : ℤ) :
  naiveBoundOn (fun x => f x + g x) (Icc a b) :=
    let bf := naiveBoundOn f (Icc a b)
    let bg := naiveBoundOn g (Icc a b)
    bf + bg
satisfied_by
  rintro b ⟨hb⟩ b' ⟨hb'⟩; constructor; rintro x ⟨h,h'⟩; simp_all;
  have := hb x h h'
  have := hb' x h h'
  sorry_proof

meta_fun_def naiveBoundsOnSub (f g : ℤ → ℤ) (a b : ℤ) :
  naiveBoundOn (fun x => f x - g x) (Icc a b) :=
    let bf := naiveBoundOn f (Icc a b)
    let bg := naiveBoundOn g (Icc a b)
    bf + bg
satisfied_by
  rintro b ⟨hb⟩ b' ⟨hb'⟩; constructor; rintro x ⟨h,h'⟩; simp_all;
  have := hb x h h'
  have := hb' x h h'
  sorry_proof

meta_fun_def naiveBoundsOnMul (f g : ℤ → ℤ) (a b : ℤ) :
  naiveBoundOn (fun x => f x * g x) (Icc a b) :=
    let bf := naiveBoundOn f (Icc a b)
    let bg := naiveBoundOn g (Icc a b)
    bf * bg
satisfied_by
  rintro b ⟨hb⟩ b' ⟨hb'⟩; constructor; rintro x ⟨h,h'⟩
  sorry_proof


/-- info: max |(-2)| |3| -/
#guard_msgs in
#eval_meta_fun naiveBoundOn (fun x => x) (Icc (-2) (3))

/--
info: let bf := |3|;
let bg := max |(-2)| |3|;
let bf := bf * bg;
let bg := max |(-2)| |3|;
bf * bg
-/
#guard_msgs in
#eval_meta_fun naiveBoundOn (fun x => (id 3)*x*x) (Icc (-2) (3))

/-- info: |3| -/
#guard_msgs in
#eval_meta_fun naiveBoundOn (fun _ => (id 3)) (Icc (-2) (3))

def getNaiveBoundOn (f : ℤ → ℤ) (s : Set ℤ) {n} (h : NaiveBoundOn f s n := by data_synth) := n

/-- info: 224 -/
#guard_msgs in
#eval getNaiveBoundOn (fun x => (x+(id 3))*(x-(id 4))*x) (Icc (-3) 4)

end NaiveBounds


section RingExpr

inductive RingExpr
  | nat (n : ℕ)
  | add (x y : RingExpr)
  | mul (x y : RingExpr)
  | pow (x : RingExpr) (n : ℕ)
  | atom (i : ℕ)
deriving Inhabited

def RingExpr.toRing {R : Type} [Ring R] (atoms : List R) (e : RingExpr) : R :=
  match e with
  | .nat n => n
  | .add x y => x.toRing atoms + y.toRing atoms
  | .mul x y => x.toRing atoms * y.toRing atoms
  | .pow x n => (x.toRing atoms)^n
  | .atom i => atoms.getD i 0

def RingExpr.toString (e : RingExpr) : String :=
  match e with
  | .nat n => s!"{n}"
  | .add x y => s!"({x.toString} + {y.toString})"
  | .mul x y => s!"({x.toString} * {y.toString})"
  | .pow x n => s!"{x.toString}^{n}"
  | .atom i => s!"#{i}"

meta_fun_decl liftRingExpr {R : Type} [Ring R] (atoms : List R) (x : R) : RingExpr
satisfying
  liftRingExpr.toRing atoms = x

meta_fun_decl atomId {R : Type} [Ring R] (atoms : List R) (x : R) : ℕ
satisfying
  atoms[atomId]? = x

-- base case
meta_fun_def atomIdBase {R : Type} [Ring R] (atoms : List R) (x : R) :
    atomId (x :: atoms) x := 0
satisfied_by
  constructor; simp_all

-- inductive
meta_fun_def atomIdSucc {R : Type} [Ring R] (atoms : List R) (x y : R) :
    atomId (y :: atoms) x := (atomId atoms x) + 1
satisfied_by
  intro i hi; constructor; simp_all[hi.1]


meta_fun_def liftRingExprAtom {R : Type} [Ring R] (atoms : List R) (x : R) :
    liftRingExpr atoms x := .atom (atomId atoms x)
satisfied_by
  intro i hi; constructor; simp_all[hi.1, RingExpr.toRing]

meta_fun_def liftRingExprMul {R : Type} [Ring R] (atoms : List R) (x y: R) :
    liftRingExpr atoms (x*y) := .mul (liftRingExpr atoms x) (liftRingExpr atoms y)
satisfied_by
  intro xe hx ye hy; constructor
  simp_all[hx.1, hy.1, RingExpr.toRing]

meta_fun_def liftRingExprAdd {R : Type} [Ring R] (atoms : List R) (x y: R) :
    liftRingExpr atoms (x+y) := .add (liftRingExpr atoms x) (liftRingExpr atoms y)
satisfied_by
  intro xe hx ye hy; constructor
  simp_all[hx.1, hy.1, RingExpr.toRing]


variable (x y : Int)


/-- info: RingExpr.atom 0 -/
#guard_msgs in
#eval_meta_fun liftRingExpr [x] (x)

/-- info: RingExpr.atom 0 -/
#guard_msgs in
#eval_meta_fun liftRingExpr [x,y] (x)

/-- info: RingExpr.atom (0 + 1) -/
#guard_msgs in
#eval_meta_fun liftRingExpr [y,x] (x)

/--
info: ((RingExpr.atom 0).mul (RingExpr.atom (0 + 1))).add
  (((RingExpr.atom 0).mul (RingExpr.atom 0)).mul (RingExpr.atom (0 + 1)))
-/
#guard_msgs in
#eval_meta_fun liftRingExpr [x,y] (x*y + x*x*y)


variable {R : Type} [Ring R]

def ringToString (atoms : List R) (x : R) {e} (he : LiftRingExpr atoms x e := by data_synth) : String :=
  e.toString

opaque a : Int
opaque b : Int

/-- info: "((#0 * #1) + ((#0 * #0) * #1))" -/
#guard_msgs in
#eval ringToString [a,b] (a*b + a*a*b)

end RingExpr


-- section ProdAssoc

-- meta_fun_decl prodAssoc (X : Type) : Type
-- satisfying
--   X ≃ prodAssoc

-- -- low priority
-- meta_fun_def (priority:=low) prodReassocSelf (X : Type) :
--   prodAssoc X := X
-- satisfied_by
--   constructor
--   exact Equiv.refl X

-- meta_fun_def (priority:=high) prodReassocUnitRight (X : Type) :
--   prodAssoc (X×Unit) := prodAssoc X
-- satisfied_by
--   intro X' equiv
--   constructor
--   exact (Equiv.prodPUnit X |>.trans equiv.1)

-- meta_fun_def (priority:=high) prodReassocUnitLeft (X : Type) :
--   prodAssoc (Unit×X) := prodAssoc X
-- satisfied_by
--   intro X' equiv
--   constructor
--   exact (Equiv.prodComm _ _ |>.trans (Equiv.prodPUnit X) |>.trans equiv.1)

-- meta_fun_def  prodReassocProdContinue (X Y : Type) :
--   prodAssoc (X×Y) := X × prodAssoc Y
-- satisfied_by
--   intro Y' f
--   constructor
--   exact (Equiv.prodCongr (Equiv.refl X) f.1)

-- meta_fun_def (priority:=high-1) prodReassocMain (X Y Z : Type) :
--   prodAssoc ((X×Y)×Z) := prodAssoc ((prodAssoc X) × Y × Z)
-- satisfied_by
--   intro X' f XYZ' g
--   constructor
--   exact (Equiv.prodAssoc X Y Z
--     |>.trans (Equiv.prodCongr f.1 (Equiv.refl _))
--     |>.trans g.1)


-- /-- info: ℕ -/
-- #guard_msgs in
-- #eval_meta_fun (prodAssoc ((Unit×ℕ×Unit)×Unit))

-- /-- info: ℕ × ℕ × ℕ -/
-- #guard_msgs in
-- #eval_meta_fun (prodAssoc ((((ℕ×ℕ)×Unit×ℕ)×Unit)×Unit))

-- def lassoc (x : X) {X'} (h : ProdAssoc X X' := by data_synth) : X' :=
--   h.1 x

-- /-- info: (1, 2, 3) -/
-- #guard_msgs in
-- #eval (lassoc ((1,2),(),3))

-- /-- info: 1 -/
-- #guard_msgs in
-- #eval (lassoc (1))

-- end ProdAssoc



section FDerivAt

meta_fun_decl derivAt (f : ℝ → ℝ) (x : ℝ) : ℝ
satisfying
  HasDerivAt (𝕜:=ℝ) f derivAt x

meta_fun_def derivAtId (x : ℝ) :
  derivAt (fun x => x) x := 1
satisfied_by
  sorry_proof

meta_fun_def derivAtConst (x y : ℝ) :
  derivAt (fun _ => y) x := 0
satisfied_by
  sorry_proof

meta_fun_def derivAtAdd (f g : ℝ → ℝ) (x : ℝ) :
  derivAt (fun x => f x + g x) x := derivAt f x + derivAt g x
satisfied_by
  sorry_proof

meta_fun_def derivAtMul (f g : ℝ → ℝ) (x : ℝ) :
  derivAt (fun x => f x * g x) x := derivAt f x * g x + f x * derivAt g x
satisfied_by
  sorry_proof


variable (x : ℝ)

/-- info: 1 -/
#guard_msgs in
#eval_meta_fun derivAt (fun x => x) x

/-- info: (1 * x + x * 1) * x + x * x * 1 + (0 * x + id 3 * 1) + (1 * x + x * 1) -/
#guard_msgs in
#eval_meta_fun derivAt (fun x => x*x*x + (id 3)*x + x*x) x
