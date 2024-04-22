import SciLean

#exit

import SciLean.Core.Rand.ExpectedValue

import SciLean.Core.Distribution.Basic
import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Distribution.ParametricDistribFwdDeriv
import SciLean.Core.Distribution.ParametricDistribRevDeriv
import SciLean.Core.Distribution.SurfaceDirac

import SciLean.Core.Functions.Gaussian



namespace SciLean

open Rand MeasureTheory Set BigOperators


set_default_scalar Float


attribute [ftrans_simp]
  FiniteDimensional.finrank_self FiniteDimensional.finrank_prod
  not_le ite_mul mul_ite mul_neg mul_one setOf_eq_eq_singleton
  Finset.card_singleton PUnit.default_eq_unit Finset.univ_unique Finset.sum_const
  preimage_id'
  mem_setOf_eq mem_ite_empty_right mem_inter_iff mem_ite_empty_right mem_univ mem_Ioo
  and_true


#exit

structure Segment where
  a : Vec2
  b : Vec2

@[pp_dot]
def Segment.toRef   (s : Segment) (p : Vec2) : Float := sorry

@[pp_dot]
def Segment.fromRef (s : Segment) (r : Float) : Vec2 := s.a + r•(s.b-s.a)

@[pp_dot]
def Segment.toSet (s : Segment) := segment Float s.a s.b

instance : Coe Segment (Set Vec2) :=  ⟨fun s => s.toSet⟩

def frontier_segment (s : Segment) : frontier s.toSet = {x} ∪ {y} := sorry_proof


/-- Structure containing vertices of a 2D triangle. -/
structure Triangle where
  (a b c : Vec2)

structure Triangle' (R : Type) [PlainDataType R] where
  (a b c : R^[2])

instance : Vec Float Triangle := sorry
instance : Inner Float Triangle := sorry
instance : TestFunctions Triangle := ⟨fun _ => True⟩
instance : SemiInnerProductSpace Float Triangle := SemiInnerProductSpace.mkSorryProofs
instance : Module ℝ Triangle := sorry

@[pp_dot]
def Triangle.toRef (t : Triangle) (p : Vec2) : Vec2 := sorry

@[pp_dot]
def Triangle.fromRef (t : Triangle) (q : Vec2) : Vec2 :=
    (1 - q.x - q.y) • t.a + q.x • t.b + q.y • t.c

@[pp_dot]
def Triangle.toSet (t : Triangle) : Set Vec2 :=
  { p : Vec2 | let q := t.toRef p; 0 ≤ q.x ∧ 0 ≤ q.y ∧ 1 - q.x - q.y ≤ 1 }

instance : Coe Triangle (Set Vec2) :=  ⟨fun t => t.toSet⟩
-- instance : CoeSort Triangle Type :=  ⟨fun t => t.toSet⟩

variable (x : Vec2) (t : Triangle)

/-- Normal velocity of the triangle `t` givenvelocity of its vectrices `v`.

For points `p` that are not on the boundary this function returns the normal velocity of
the closes point on the triangle boudary. -/
def Triangle.frontierSpeed (t v : Triangle) (p : Vec2) : Float :=
  -- let r₁ := closestPointRef (Segment.mk t.a t.b) p
  -- let r₂ := closestPointRef (Segment.mk t.b t.c) p
  -- let r₃ := closestPointRef (Segment.mk t.c t.a) p
  -- once we locase the closes point corresponding segment
  -- Point must go in counter-clockwise order!!!
  let a : Vec2 := sorry
  let b : Vec2 := sorry
  let va : Vec2 := sorry
  let vb : Vec2 := sorry
  let r : Vec2 := sorry
  let n := v[b.y - a.y, a.x - b.x].normalize
  let v := va + r • (vb - va)
  ⟪n, v⟫


variable
  {W} [Vec Float W]
  [MeasureSpace Vec2]
  {X} [Vec Float X] [MeasureSpace X]
  {Y} [Vec Float Y] [Module ℝ Y]


@[simp, ftrans_simp]
theorem frontierSpeed_triangle (t : W → Triangle) (w dw : W) :
    frontierSpeed Float (fun w => (t w).toSet) w dw
    =
    fun p : Vec2 =>
      let tdt := fwdDeriv Float t w dw
      tdt.1.frontierSpeed tdt.2 p := sorry_proof


def PieceWiseSmooth (f : X → Y) : Prop := sorry


/-- Normal of a segment `s`, obtained by rotating `s` around `s.a` by counter-clockwise 90° and
normalizing -/
def Segment.normal (s : Segment) : Vec2 :=
  let d := s.b - s.a
  v[-d.y, d.x].normalize


/-- Normal speed of segment `{s.a, s.b}` in normal direction at point `r` on reference
segment `[0,1]`.

Let point `s.a` moves with velocity `v.a` and point `s.b` moves with velocity `v.b`.
This function computes the normal component of the velocity at point `s.a + r•(s.b-s.a)`.
The normal of a segment is-/
@[pp_dot]
def Segment.normalSpeedRef (s v : Segment) (r : Float) : Float :=
  let n := s.normal
  ⟪v.a + r • (v.b-v.a),n⟫


#exit

-- Instrument simp to not apply this theorem if `t` is constant function
-- @[simp, ftrans_simp] -- , simp_guard t notConst]
theorem hihi' (t : W → Triangle) (f : W → Vec2 → Y) :
  fwdDeriv Float (fun w => ∫' x in (t w).toSet, f w x)
  =
  fun w dw =>
    let tdt := fwdDeriv Float t w dw
    let s₁ := Segment.mk tdt.1.a tdt.1.b
    let s₂ := Segment.mk tdt.1.b tdt.1.c
    let s₃ := Segment.mk tdt.1.c tdt.1.a
    let ds :=
      ∫' r in Ioo (0:Float) 1,
        let c₁ := s₁.normalSpeedRef ⟨tdt.2.a,tdt.2.b⟩ r • f w (s₁.fromRef r)
        let c₂ := s₂.normalSpeedRef ⟨tdt.2.b,tdt.2.c⟩ r • f w (s₂.fromRef r)
        let c₃ := s₃.normalSpeedRef ⟨tdt.2.c,tdt.2.a⟩ r • f w (s₃.fromRef r)
        (-(c₁ + c₂ + c₃)) -- negative sign because of the orientation of segment normals

    let idi := fwdDeriv Float (fun w' => ∫' x in tdt.1, f w' x) w dw

    (idi.1, idi.2 + ds) := sorry_proof


section Ohoho

variable {W : Type} [SemiInnerProductSpace Float W]
  {Y : Type} [SemiInnerProductSpace Float Y] [Module ℝ Y]

theorem hihi'' (t : W → Triangle) (f : W → Vec2 → Y) :
  revDeriv Float (fun w => ∫' x in (t w).toSet, f w x)
  =
  fun w =>
    let tdt := revDeriv Float t w
    let s₁ := Segment.mk tdt.1.a tdt.1.b
    let s₂ := Segment.mk tdt.1.b tdt.1.c
    let s₃ := Segment.mk tdt.1.c tdt.1.a

    let idi := revDeriv Float (fun w' => ∫' x in tdt.1, f w' x) w

    (idi.1, fun dy =>

      let dt' : Triangle :=
        ∫' r in Ioo (0:Float) 1,
          let c₁ := ⟪f w (s₁.fromRef r), dy⟫ • Triangle.mk ((1-r)•s₁.normal) (r•s₁.normal) 0
          let c₂ := ⟪f w (s₂.fromRef r), dy⟫ • Triangle.mk 0 ((1-r)•s₂.normal) (r•s₂.normal)
          let c₃ := ⟪f w (s₃.fromRef r), dy⟫ • Triangle.mk (r•s₃.normal) 0 ((1-r)•s₃.normal)
          (-(c₁ + c₂ + c₃))

      idi.2 dy + tdt.2 dt') := sorry_proof

end Ohoho


@[simp, ftrans_simp]
theorem hihi (A : Set X) (f : W → X → Y) :
  fwdDeriv Float (fun w => ∫' x in A, f w x)
  =
  fun w dw =>
    (∫' x in A, fwdDeriv Float (f · x) w dw) := sorry_proof


@[simp, ftrans_simp]
theorem frontier_triangle {t : Triangle} :
  frontier (t.toSet)
  =
  (Segment.mk t.a t.b).toSet ∪ (Segment.mk t.b t.c).toSet ∪ (Segment.mk t.c t.a).toSet := sorry_proof

variable [MeasureSpace Vec2] (t : Triangle) (f : Vec2 → Float)


set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.simp.discharge true in
#check (∂> t : Triangle, ∫' p in t, f p)
  rewrite_by
    rw [hihi']
    simp (config:={zeta:=false}) only [ftrans_simp]
