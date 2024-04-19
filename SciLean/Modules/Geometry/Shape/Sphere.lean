import SciLean.Modules.Geometry.Shape

namespace SciLean

namespace Shape

variable
  {R : Type _} [RealScalar R]
  {X : Type _} [SemiHilbert R X]
  {Y : Type _} [SemiHilbert R Y]
  {S : Type _} [Shape S X]

------------------------------------------------------------------------------
-- Sphere and Ball
------------------------------------------------------------------------------

/-- Sphere with center `c` and radius `r`. -/
structure Sphere (R : Type u) (X : Type v) where
  c : X
  r : R

structure Ball (R : Type u) (X : Type v) where
  c : X
  r : R

def Sphere.toBall (s : Sphere R X) : Ball R X := {
  c := s.c
  r := s.r
}

def Ball.toSphere (s : Ball R X) : Sphere R X := {
  c := s.c
  r := s.r
}


instance : Shape (Sphere R X) X where
  toSet s := {x | ‖x-s.c‖₂[R] = s.r}

instance : Shape (Ball R X) X where
  toSet s := {x | ‖x-s.c‖₂[R] ≤ s.r}


------------------------------------------------------------------------------
-- Bounding Sphere
------------------------------------------------------------------------------

variable (R) (X) (S)
class BoundingSphere where
  /-- The smallest sphere containing the shape `s` -/
  boundingSphere (s : S) : Sphere R X
  is_bounding_sphere :
    ∀ (s : S),
      let b := (boundingSphere s).toBall;
      -- is bounding
      toSet s ⊆ toSet b
      ∧
      -- is minimal
      ∀ (b' : Ball R X), toSet s ⊆ toSet b' → toSet b ⊆ toSet b'
variable {S} {R} {X}

export BoundingSphere (boundingSphere)

variable (R)
abbrev boundingBall [BoundingSphere R X S] (s : S) : Ball R X := (boundingSphere (R:=R) s).toBall
variable {R}



variable [PlainDataType R]

def _root_.IndexType.argValMax {I} [IndexType.{_,0} I] [Inhabited I]
    (f : I → X) [LT X] [∀ x x' : X, Decidable (x<x')] : I×X :=
  IndexType.reduceD
    (fun i => (i,f i))
    (fun (i,e) (i',e') => if e < e' then (i',e') else (i,e))
    (default, f default)

def _root_.IndexType.argMax {I} [IndexType.{_,0} I] [Inhabited I]
    (f : I → X) [LT X] [∀ x x' : X, Decidable (x<x')] : I :=
  (IndexType.argValMax f).1


set_default_scalar R


variable (R)
def vecNormalize {X} [SemiHilbert R X] (x : X) : X := (‖x‖₂[R])⁻¹ • x
variable {R}



/-- Given collection of `m` vectors  -/
def gramSchmidt {X} [SemiHilbert R X] [PlainDataType X] (u : X^[n]) : X^[n] := Id.run do
  let mut u := u
  for i in IndexType.univ (Fin n) do
    let mut ui := u[i]
    for j in [0:i.1] do
      let j : Fin n := ⟨j,sorry_proof⟩
      let uj := u[j]
      ui -= ⟪uj,ui⟫ • uj
    u[i] := vecNormalize (R:=R) ui
  return u


-- /-- Decompose `R^[n]` into the plane `{x | ⟪u,x⟫ + c = 0}` and its orthogonal complement.

--  -/
-- def planeDecomposition (u : R^[n]) (c : R) : R×R^[n-1] ≃ R^[n] := Id.run do
--   if h : n = 0 then
--     sorry
--   else
--     have : Inhabited (Fin n) := ⟨0, sorry⟩
--     let i := IndexType.argMax (fun i => Scalar.abs (u[i]))
--     let mut basis : R^[n]^[n-1] := ⊞ (j : Fin (n-1)) => (⊞ (i' : Fin n) =>
--       if j.1 < i.1 then
--         if j.1 = i'.1 then (1:R) else 0
--       else
--         if j.1 +1 = i'.1 then 1 else 0)

--     let u' := vecNormalize R u

--     for i in IndexType.univ (Fin (n-1)) do
--       let mut v := basis[i]
--       v -= ⟪v,u'⟫ • u'
--       for j in [0:i.1] do
--         let j : Fin (n-1) := ⟨j, sorry_proof⟩
--         basis[j] :=
--       pure ()

-- variable (u : R^[n])

-- #check fun (i : Fin n) => u[i]

-- #eval ⊞[(1:Float),2,3,4,5,6].reshape (Fin 2 × Fin 3) (by decide)

-- def A := ⊞[(1:Float),2,3,1,0,0,0,1,0].reshape (Fin 3 × Fin 3) (by decide) |>.curry
-- def a := gramSchmidt (R:=Float) <| A

-- set_default_scalar Float


-- #eval a


-- #eval ‖A[0]‖₂

-- #eval ‖A[0]‖₂ • a[0]
-- #eval ‖a[0]‖₂


-- #eval a[1]
-- #eval ‖a[1]‖₂

-- #eval ⟪a[1],a[0]⟫
