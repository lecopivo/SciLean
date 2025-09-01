import SciLean.Modules.Geometry.Shape
import SciLean.Modules.Geometry.Shape.Sphere
import SciLean.Modules.Geometry.Shape.AxisAlignedBox
import SciLean.Tactic.InferVar

open FiniteDimensional

namespace SciLean

namespace Shape

variable
  {R : Type _} [RealScalar R] [PlainDataType R]
  {ι : Type _} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {X : Type _} [FinVec ι R X] [PlainDataType X]
  {Y : Type _} [SemiHilbert R Y]
  {S : Type _} [Shape S X]

set_default_scalar R

-- instance : GetElem X ι R (fun _ _ => True) where
--   getElem x i _ := ℼ i x

-- instance : GetElem X ℕ R (fun _ i => i < IndexType.card ι) where
--   getElem x i h := ℼ (IndexType.fromFin ⟨i,h⟩) x


variable (R) (X)
structure Triangle where
  (a b c : X)
  hdim : finrank R X = 2 := by first | simp | decide
variable {R} {X}


/-- This theorem is usually used as `have := t.hdim'`. This adds to the contex that the
dimension of `X` is equal to 2 and allows you to use index notation e.g. `t.a[0]`.  -/
theorem Triangle.hdim' (t : Triangle R X) : IndexType.card ι = 2 := sorry_proof


instance : Shape (Triangle R X) X where
  toSet t p := ∃ (x y z : Set.Icc (0:R) 1),
    (x.1 + y.1 + z.1 = 1)
    ∧
    (x.1 • t.a + y.1 • t.b + z.1 • t.c = p)


def Triangle.area (t : Triangle R X) : R :=
  have := t.hdim'
  (0.5:R) *(-t.b[1]*t.c[0] + t.a[1]*(-t.b[0] + t.c[0]) + t.a[0]*(t.b[1] - t.c[1]) + t.b[0]*t.c[1])


def Triangle.baryCoord (t : Triangle R X) (x : X) : R^[3] :=
  have := t.hdim'
  let a := 1/(2*t.area)
  let s := a*(t.a[1]*t.c[0] - t.a[0]*t.c[1] + (t.c[1] - t.a[1])*x[0] + (t.a[0] - t.c[0])*x[1])
  let t := a*(t.a[0]*t.b[1] - t.a[1]*t.b[0] + (t.a[1] - t.b[1])*x[0] + (t.b[0] - t.a[0])*x[1])
  ⊞[1-s-t,s,t]


instance : Locate (Triangle R X) where
  locate t x :=
    let cx := t.baryCoord x
    -- notation cx[i] breaks here for some reason :(
    if 0 ≤ cx.get 0 ∧ 0 ≤ cx.get 1 ∧ 0 ≤ cx.get 2 then
      if 0 = cx.get 0 ∨ 0 = cx.get 1 ∨ 0 = cx.get 2 then
        .boundary
      else
        .inside
    else
      .outside
  is_locate := sorry_proof


instance (t : Triangle R X) (x : X) : Decidable (x ∈ toSet t) :=
  match locate t x with
  | .inside | .boundary => .isTrue sorry_proof
  | .outside => .isFalse sorry_proof


instance (t : Triangle R X) (s : Triangle R X) : Decidable (toSet s ⊆ toSet t) :=
  if s.a ∈ toSet t &&
     s.b ∈ toSet t &&
     s.c ∈ toSet t then
     .isTrue sorry_proof
  else
    .isFalse sorry_proof


open RealScalar Scalar in
def Triangle.circumCenter (t : Triangle R X) : X :=
  let a : R := ‖t.b - t.c‖₂[R]
  let b : R := ‖t.c - t.a‖₂[R]
  let c : R := ‖t.a - t.b‖₂[R]
  let α : R := acos ((b^2 + c^2 - a^2) / (2*b*c))
  let β : R := acos ((c^2 + a^2 - b^2) / (2*c*a))
  let γ : R := acos ((a^2 + b^2 - c^2) / (2*a*b))

  let aw := sin (2*α)
  let bw := sin (2*β)
  let cw := sin (2*γ)
  let w := (aw+bw+cw)⁻¹
  let aw := w*aw
  let bw := w*bw
  let cw := w*cw

  aw • t.a + bw • t.b + cw • t.c


def Triangle.circumCircle (t : Triangle R X) : Sphere R X := {
  center := t.circumCenter
  radius := ‖t.circumCenter - t.a‖₂
}


def Triangle.isAcute (t : Triangle R X) : Bool :=
  let a2 := ‖t.b - t.c‖₂²
  let b2 := ‖t.c - t.a‖₂²
  let c2 := ‖t.a - t.b‖₂²

  (a2 < b2 + c2) ∧ (c2 < a2 + b2) ∧ (b2 < c2 + a2)


open Scalar in
instance : BoundingSphere (Triangle R X) where
  boundingSphere t :=
    if t.isAcute then
      t.circumCircle
    else Id.run do
      let a2 := ‖t.b - t.c‖₂²
      let b2 := ‖t.c - t.a‖₂²
      let c2 := ‖t.a - t.b‖₂²
      if b2 ≤ a2 ∧ c2 ≤ a2 then
        return { center := (0.5:R) • (t.b+t.c), radius := (sqrt a2)/2 }
      if a2 ≤ b2 ∧ c2 ≤ b2 then
        return { center := (0.5:R) • (t.a+t.c), radius := (sqrt b2)/2 }
      if b2 ≤ c2 ∧ a2 ≤ c2 then
        return { center := (0.5:R) • (t.a+t.b), radius := (sqrt c2)/2 }
      unreachable!

  is_bounding_sphere := sorry_proof


open IndexType in
instance [OrthonormalBasis ι R X] : BoundingBox (Triangle R X) where
  boundingBox t :=
    have := t.hdim'
    { min := (min t.a[0] (min t.b[0] t.c[0])) • ⅇ (fromFin ⟨0,sorry_proof⟩) +
             (min t.a[1] (min t.b[1] t.c[1])) • ⅇ (fromFin ⟨1,sorry_proof⟩),
      max := (max t.a[0] (max t.b[0] t.c[0])) • ⅇ (fromFin ⟨0,sorry_proof⟩) +
             (max t.a[1] (max t.b[1] t.c[1])) • ⅇ (fromFin ⟨1,sorry_proof⟩) }
  is_bounding_box := sorry_proof


@[pp_dot]
def _root_.Set.prodDep {α β} (A : Set α) (B : α → Set β) : Set (α×β) :=
  {ab | ab.1 ∈ A ∧ ab.2 ∈ B ab.1}

@[simp, ftrans_simp]
theorem _root_.LeanColls.IndexType.card_unit : IndexType.card Unit = 1 := by rfl

@[simp, ftrans_simp]
theorem _root_.LeanColls.IndexType.card_sum {ι κ} [IndexType ι] [IndexType κ] :
    IndexType.card (ι ⊕ κ) = IndexType.card ι + IndexType.card κ := by rfl

@[simp, ftrans_simp]
theorem _root_.LeanColls.IndexType.card_prod {ι κ} [IndexType ι] [IndexType κ] :
    IndexType.card (ι × κ) = IndexType.card ι * IndexType.card κ := by rfl


-- /-- Given collection of `m` vectors  -/
-- def gramSchmidtDataArrayImpl {X} [SemiHilbert R X] [PlainDataType X] (u : X^[n]) : X^[n] := Id.run do
--   let mut u := u
--   for i in IndexType.univ (Fin n) do
--     let mut ui := u[i]
--     for j in [0:i.1] do
--       let j : Fin n := ⟨j,sorry_proof⟩
--       let uj := u[j]
--       ui -= ⟪uj,ui⟫ • uj
--     u[i] := vecNormalize (R:=R) ui
--   return u


open IndexType Scalar in
/-- Given a plane `{x | ⟪u,x⟫=0}` this function decomposes `R^[n]` into this plane and its
orthogonal complement.

TODO: Fix this function for `u = 0`!!! -/
def planeDecomposition
    {n} {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι] {X} [FinVec ι R X]
    (u : X)
    (hn : n + 1 = card ι := by first | assumption | infer_var) :
    R×R^[n] ≃ X := Id.run do

  have : Inhabited ι := ⟨fromFin ⟨0, by omega⟩⟩

  let i' := toFin (IndexType.argMax (fun i : ι => |u[i]|))

  -- Initiali collection of basis vectors
  -- `u` is take as the first basis vector
  -- and we complete it with the canonical bases on `R^[n]` but we omit the basis vector
  -- that corresponds to the largest component of `u`
  let basis : Array X := .ofFn fun (i : Fin (n+1)) =>
    if i.1 = 0 then
      u
    else if i.1 ≤ i'.1 then
      let i'' : ι := fromFin ⟨i.1-1, sorry_proof⟩
      ⅇ i''
    else
      let i'' : ι := fromFin ⟨i.1, sorry_proof⟩
      ⅇ i''

  let basis := gramSchmidtArrayImpl (R:=R) basis

  {
    toFun := fun (t,y) =>
      t • basis.get ⟨0,sorry_proof⟩
      +
      ∑ i : Fin n, y.get i • basis.get ⟨i.1+1, sorry_proof⟩
    invFun := fun x =>
      (⟪x,basis.get ⟨0,sorry_proof⟩⟫, ⊞ (j : Fin n) => ⟪x, basis.get ⟨j.1+1, sorry_proof⟩⟫)
    left_inv := sorry_proof
    right_inv := sorry_proof
  }

def dec := planeDecomposition (R:=Float) (1.0,2.0,3.0)

#eval dec (1, 0)
#eval dec (3, ⊞[(0.0:Float),0.0])
#eval dec.symm (1.0, 2.0, 3.0)

open IndexType in
theorem planeDecomposition_normal_dir
    {n} {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
    {X} [FinVec ι R X]
    (u : X)
    (hn : n + 1 = card ι) :
    planeDecomposition (R:=R) u hn (t,0) = (t • vecNormalize R u) := sorry_proof

open IndexType in
theorem planeDecomposition_orthogonal_dir
    {n} {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι] {X} [FinVec ι R X]
    (u : X) (y : R^[n])
    (hn : n + 1 = card ι) :
    ⟪u, planeDecomposition (R:=R) u hn (0,y)⟫ = 0 := sorry_proof

open Scalar IndexType in
@[simp, ftrans_simp]
theorem planeDecomposition.arg_x.ball_preimage_rule {n} (u : X) (s : Ball R X)
    (hn : n + 1 = card ι) :
    (planeDecomposition (R:=R) u hn)⁻¹' (toSet s)
    =
    let (tc, yc) := (planeDecomposition (R:=R) u hn).symm s.center
    let A := Set.Icc (tc - s.radius) (tc + s.radius)
    let B := fun t : R => toSet (Ball.mk yc (sqrt (s.radius^2 - (t-tc)^2)))
    A.prodDep B := sorry_proof





def t : Triangle Float (Float×Float) := Triangle.mk (0.0231,0.01554) (1.0124,0.0125) (-10.054,1.0123)

#eval t.isAcute
#eval boundingSphere t
#eval boundingBox t

#eval ‖(boundingSphere t).center - t.a‖₂[Float]
#eval ‖(boundingSphere t).center - t.b‖₂[Float]
#eval ‖(boundingSphere t).center - t.c‖₂[Float]

#eval t.circumCircle
