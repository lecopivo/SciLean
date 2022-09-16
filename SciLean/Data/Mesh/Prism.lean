import SciLean.Prelude
import SciLean.Mathlib.Data.Enumtype
import SciLean.Algebra

namespace SciLean

/-- Prism

  A prism is anything that can be created from a point and two operations: cone and product. This way we can basic geometric primitives like triangles, squares, pyramids, n-simplices, n-cubes etc.




```
    *   = point

    *
   / \  = cone *--*
  *---*

  *--*          *
  |  |  = prod  |   *--*
  *--*          *
```

  segment  = cone point  
  triangle = cone segment
  square   = prod segment segment
  cube     = prod segment square
  tet      = cone triangle
  pyramid  = cone square

  n-simples = coneⁿ point 
  n-cube    = (prod segment)ⁿ⁻¹ segment

  Non-uniqueness
  --------------

  TODO: This definition needs to be factored

  Cartain prisms have multiple different representations. For example `cube = prod segment square ≈ prod square segment`. This is the reason this inductive type is only a representation and not the final prism.

 -/
inductive Prism where
  | point : Prism
  | cone (P : Prism) : Prism
  | prod (P Q : Prism) : Prism
deriving DecidableEq

namespace Prism

  /-- Number of `n`-dimensional faces of prism `P` -/
  def faceCount (P : Prism) (n : Nat) : Nat :=
    match P with
    | point => if n == 0 then 1 else 0
    | cone P => 
      match n with
      | 0   => 1 + P.faceCount 0
      | n+1 => P.faceCount n + P.faceCount (n+1)
    | prod P Q => ∑ i : Fin (n+1), (P.faceCount i.1) * (Q.faceCount (n-i.1))

  /-- Dimension of a prism -/
  def dim : (P : Prism) → Nat
    | point => 0
    | cone P' => 1 + P'.dim
    | prod P' Q' => P'.dim + Q'.dim

  /-- 
    The type `Face P` represends faces of a prism `P` 

    Point prism can have only one face, the point itself.

    Cone prisms have three types of faces.
      1. the tip
      2. sides of the code
      3. faces of the base prism
    
    Product prisms have faces are created by products of 

    Categorical perspective
    -----------------------

    A face is a inclusion of a prism `F` into a prism `P`. For a face `f : Face P`, we can obtain `F` by `f.toPrism`.
    
    Then we can thin about `f` as a morphism `F → P` in the `Prism` category.
  -/
  inductive Face : Prism → Type where
    | point : Face point
    | tip (P : Prism) : Face (cone P)
    | cone {P : Prism} (f : Face P) : Face (cone P)
    | base {P : Prism} (f : Face P) : Face (cone P)
    | prod {P Q : Prism} (f : Face P) (g : Face Q) 
      : Face (prod P Q)
  deriving DecidableEq

  namespace Face

/--
A face of a prism is again a prism. This function converts 

---

Categorical perspective
-----------------------

A face is a inclusion of a prism `F` into a prism `P`. For a face `f : Face P`, we can obtain `F` by `f.toPrism`.

Then we can thin about `f` as a morphism `F → P` in the `Prism` category.
-/
    def toPrism {P} (f : Face P) : Prism :=
      match f with
      | point => Prism.point
      | tip P  => Prism.point
      | cone f => Prism.cone f.toPrism
      | base f => f.toPrism
      | prod f g => Prism.prod f.toPrism g.toPrism

    /-- Dimension of a prism -/
    def dim {P} (f : Face P) : Nat := f.toPrism.dim

    /-- Face of a face is a face. For further details see `Face.ofFace` -/
    def ofFace' {P Q : Prism}
      (f : Face P) (g : Face Q) (h : f.toPrism = Q) 
      : Face P
      :=
        match f, g, h with 
        |   point,   point, _ => point
        |  tip P',   point, _ => tip P'
        | cone f',   tip _, _ => tip _
        | cone f', cone g', h => 
          cone (ofFace' f' g' (by simp[toPrism] at h; apply h))
        | cone f', base g', h => 
          base (ofFace' f' g' (by simp[toPrism] at h; apply h))
        | base f',      g', h => 
          base (ofFace' f' g' (by simp[toPrism] at h; apply h))
        | prod f' f'', prod g' g'', h => 
          prod (ofFace' f' g' (by simp[toPrism] at h; apply h.1)) 
               (ofFace' f'' g'' (by simp[toPrism] at h; apply h.2))

/--
Face of a face is a face. If we have a face `f` of prism `P` and a face `g` of prism `f.toPrism` then `g` is also a face of `P`.


---

Categorical perspective
----------------------- 
This is morphism composition. The face `f` is a morphism `Q → P` and `g` is a morphism `S → Q`. Then `g.ofFace : Face P` is just a composition `f∘g` in the `Prism` category.
-/

    def ofFace {P} {f : Face P} (g : Face f.toPrism) : Face P
      := ofFace' f g (by rfl)

    example {P} (f : Face P) (g : Face f.toPrism) : Face P := ofFace g
    -- TODO: Fix this, g.ofFace get interpreted as `ofFace (f := g)`
    -- example {P} (f : Face P) (g : Face f.toPrism) : Face P := g.ofFace

    /-- The prism type of a face does not depend on the larger prism. -/
    @[simp]
    theorem toPrism_ofFace {P} {f : Face P} (g : Face f.toPrism) 
      : Face.toPrism (Face.ofFace g) = Face.toPrism g
      := sorry

    /-- The first `n`-face of `P` -/
    def first (P : Prism) (n : Nat) : Option (Face P) :=
      match P, n with
      | Prism.point, 0 => some point
      | Prism.point, _ => none
      | Prism.cone P', 0 => some (tip P')
      | Prism.cone P', n'+1 => 
        match first P' n' with
        | some f => some $ (cone f)
        | none => none
      | Prism.prod P' Q', n =>
        Id.run do
        for i in [0:n+1] do
          match first P' i, first Q' (n-i) with
          | some f', some g' =>
            return some $ (prod f' g')
          | _, _ => continue
        none

    /-- The dimension of the first `n`-face is really `n` -/
    theorem first.dim (P: Prism) (n : Nat) (h : n ≤ P.dim)
      : (Face.first P n).map (·.dim)  = some n := sorry

    /-- The next face of the same dimension -/
    def next {P} (f : Face P) : Option (Face P) := 
      match P, f.dim, f with
      | Prism.point, 0, point => none
      | Prism.cone P', 0, tip _ => 
        match first P' 0 with
        | some f' => some $ base f'
        | none => none
      | Prism.cone P', n'+1, cone f' => 
        match next f' with
        | some f'' => some $ cone f''
        | none => 
          match first P' (n'+1) with
          | some f'' => some $ base f''
          | none => none
      | Prism.cone P', n', base f' => 
        match next f' with
        | some f'' => some $ base f''
        | none => none
      | _, _, @prod P' Q' f' g' => 
        match next f' with
        | some f'' => some $ prod f'' g'
        | none => 
          match first P' f'.dim, next g' with
          | some f'', some g'' => some $ Face.prod f'' g''
          | _, _ => 
            match g'.dim with
            | 0 => none
            | m''+1 => 
              match first P' (f'.dim+1), first Q' m'' with
              | some f'', some g'' => some $ Face.prod f'' g''
              | _, _ => none
      | _, _, _ => panic! "Unreachable code in Face.next. This is a bug!"

    instance {P} : Iterable (Face P) :=
    {
      first := first P 0
      next := λ f =>
        match next f with
        | some f' => some f'
        | none => 
          match first P (f.dim + 1) with
          | some f' => some f'
          | none => none
      decEq := by infer_instance
    }

    /-- Index of a face amog faces of the same dimension -/
    def toFin {P} (f : Face P) : Fin (P.faceCount f.dim) := 
      match P, f.dim, f with
      | _, _, point => ⟨0, sorry⟩
      | _, _, tip _ => ⟨0, sorry⟩
      | _, _, cone f' => ⟨f'.toFin.1, sorry⟩
      | Prism.cone P', 0, base f' => ⟨1+f'.toFin.1, sorry⟩
      | Prism.cone P', n'+1, base f' => ⟨(P'.faceCount n')+f'.toFin.1, sorry⟩
      | _, _, @prod P' Q' f' g' => 
        ⟨(∑ i : Fin f'.dim, (P'.faceCount i)*(Q'.faceCount (f.dim-i)))
         + f'.toFin.1 + g'.toFin.1 * (P'.faceCount f'.dim), sorry⟩

  end Face

  /-- Face of fixed dimension -/
  def NFace (P : Prism) (n : Nat) := {f : Face P // f.dim = n}

  namespace NFace

    instance {P} : DecidableEq (NFace P n) := by simp[NFace] infer_instance done

    def first {P n} : Option (NFace P n) :=
      match Face.first P n with
      | some f' => some !f'
      | none => none

    def next {P n} (f : NFace P n) : Option (NFace P n) :=
      match f.1.next with
      | some f' => some !f'
      | none => none

    instance {P n} : Iterable (NFace P n) :=
    {
      first := first
      next := next
      decEq := by infer_instance
    }

    def toFin {P n} (f : NFace P n) : Fin (P.faceCount n) := (f.2 ▸ f.1.toFin)

    -- def Face.fromFin (P : Prism) (n : Nat) (i : Fin (P.faceCount n)) : Face P n := 
    --   match P, n, i with
    --   | Prism.point, 0, _ => point
    --   | Prism.cone P', 0, _ => 
    --     if i.1=0 then 
    --       tip _ 
    --     else 
    --       base (fromFin P' 0 ⟨i.1-1, sorry⟩)
    --   | Prism.cone P', n'+1, _ => 
    --     let offset := P'.faceCount n'
    --     if i.1 < offset then 
    --       cone (fromFin P' n' ⟨i.1, sorry⟩)
    --     else 
    --       base (fromFin P' (n'+1) ⟨i.1 - offset, sorry⟩)
    --   | Prism.prod P' Q', n, _=> Id.run do
    --     let mut offset := 0
    --     for j in [0:n+1] do
    --       let pfc := (P'.faceCount j)
    --       let qfc := (Q'.faceCount (n-j))
    --       let jcount := pfc * qfc
    --       if i.1 < offset + jcount then
    --         let i' := (i.1 - offset) % pfc
    --         let j' := (i.1 - offset) / pfc
    --         let r  := (prod (fromFin P' j ⟨i', sorry⟩) 
    --                         (fromFin Q' (n-j) ⟨j', sorry⟩))
    --         return ((sorry : j+(n-j)=n) ▸ r)
    --       else
    --         offset := offset + jcount
    --         continue
    --     sorry
    --     -- panic! "This should be unreachable!"

  end NFace

  def segment  := cone point
  def triangle := cone segment
  def square   := prod segment segment
  def tet      := cone triangle
  def cube     := prod segment square
  def pyramid  := cone square
  def prism    := prod segment triangle

  #eval (
    (do
      let mut it := Face.first prism 2
      for i in [0:100] do
        match it with
        | some f => do
          IO.print s!"{f.toFin}: "
          let mut jt := Face.first f.toPrism 0
          for j in [0:100] do
            match jt with
            | some g => 
              IO.print s!"{g.ofFace.toFin} "
              jt := g.next
            | none => break
          IO.println ""
          it := f.next
        | none => break
    ) : IO Unit)

  -- Natural embedding space
  def 𝔼 : (P : Prism) → Type
    | point => Unit
    | cone P' => ℝ × P'.𝔼
    | prod P' Q' => P'.𝔼 × Q'.𝔼

  instance E.Vec (P : Prism) : Vec P.𝔼 :=
    match P with
    | point => by simp[𝔼]; infer_instance done
    | cone P => by simp[𝔼]; apply (@instVecProd _ _ (by infer_instance) (Vec P)); done
    | prod P Q => by simp[𝔼]; apply (@instVecProd _ _ (Vec P) (Vec Q)); done

  def pointCount (P : Prism) : Nat := P.faceCount 0

  def barycenter (P : Prism) : P.𝔼 :=
    match P with
    | point => 0
    | cone P' => 
      let w := (1.0 : ℝ)/(P.pointCount : ℝ)
      (w, (1-w)*P'.barycenter)
    | prod P Q =>
      (P.barycenter, Q.barycenter)

  def pos {P : Prism} : NFace P 0 → P.𝔼 := sorry
  -- def pos {P : Prism} : Fin (P.pointCount) → ℝ^P.dim := sorry

  -- def toRn : {P : Prism} → P.E → ℝ^P.dim := sorry
  -- def fromRn : {P : Prism} → ℝ^P.dim → P.E := sorry

  def barycentricCoord {P : Prism} (p : NFace P 0) (x : P.𝔼) : ℝ := 
    match P, p, x with
    | point, _, _ => 0
    | cone P', ⟨Face.tip _, _⟩, (t, x') => t
    | cone P', ⟨Face.base p', _⟩, (t, x') => 
      t * (barycentricCoord (!p' : NFace P' 0) x')
    | prod P Q, ⟨Face.prod p q, _⟩, (x, y) => 
      (barycentricCoord (!p : NFace P 0) x) * 
      (barycentricCoord (!q : NFace Q 0) y)
    | _, _, _ => 0 -- This should be unreachable!

  -- def barycentricCoord {P : Prism} : Fin (P.pointCount) → ℝ^P.dim → ℝ := sorry

  -- embedding map from a face to prism
  def Face.embed {P} (f : Face P) : f.toPrism.𝔼 → P.𝔼 := sorry


  -- order preserving map from one prism to another prism
  -- Should include pure inclusions like Face but also collapses
  -- 
  -- There is some non-uniqueness, doing `shift` if the same as `cone ∘ base`
  inductive Morph : Prism → Type
    | point : Morph point
    | tip (P : Prism) : Morph (cone P)
    | cone {P : Prism} (f : Morph P) : Morph (cone P)
    | base {P : Prism} (f : Morph P) : Morph (cone P)
    | collapse {P : Prism} (m : Morph (cone P)) : Morph (cone (cone P))
    | shift    {P : Prism} (m : Morph (cone P)) : Morph (cone (cone P))
    | prod {P Q : Prism} (f : Morph P) (g : Morph Q) : Morph (prod P Q)

  -- Face if Morph not containing collapses and shifts

