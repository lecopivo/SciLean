import SciLean.Prelude
import SciLean.Mathlib.Data.Enumtype
import SciLean.Data.EnumType
-- import SciLean.Algebra
import SciLean.Core.Vec

def List.bubblesort [LT α] [DecidableRel (. < . : α → α → Prop)] (l : List α) : {l' : List α // l.length = l'.length} :=
  match l with
  | [] => ⟨[], rfl⟩
  | x :: xs =>
    match xs.bubblesort with
    | ⟨[], h⟩ => ⟨[x], by simp[h]⟩
    | ⟨y :: ys, h⟩ =>
      if y < x then
        have : Nat.succ (length ys) < Nat.succ (length xs) := by rw [h, List.length_cons]; apply Nat.lt_succ_self
        let ⟨zs, he⟩ := bubblesort (x :: ys)
        ⟨y :: zs, by simp[h, ← he]⟩
      else
        ⟨x :: y :: ys, by simp[h]⟩
decreasing_by sorry_proof
-- termination_by _ => l.length  -- clashes with Mathlib.Data.List.Basic

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
inductive PrismRepr where
  | point : PrismRepr
  | cone (P : PrismRepr) : PrismRepr
  | prod (P Q : PrismRepr) : PrismRepr
with
  /-- Dimension of a prism -/
  @[computed_field]
  dim : (P : PrismRepr) → Nat
  | .point => 0
  | .cone P' => P'.dim + 1
  | .prod P' Q' => P'.dim + Q'.dim
deriving DecidableEq, Inhabited

def PrismRepr.dim' (P : PrismRepr) : USize :=
  if P.dim < USize.size then
    P.dim.toUSize
  else
    (USize.size-1).toUSize

section PrismExamples
  open PrismRepr

  private def segment  := cone point
  private def triangle := cone segment
  private def square   := prod segment segment
  private def tet      := cone triangle
  private def cube     := prod segment square
  private def pyramid  := cone square
  private def prism    := prod segment triangle

  private def ncube : (dim : Nat) → PrismRepr
  | 0 => point
  | 1 => segment
  | (n+1) => prod segment (ncube n)

  private def ntet : (dim : Nat) → PrismRepr
  | 0 => point
  | (n+1) => cone (ntet n)

end PrismExamples

namespace PrismRepr

  /-- Number of `n`-dimensional faces of prism `P` -/
  def faceCount (n : Nat) (P : PrismRepr) : Nat :=
    match P with
    | point => if n == 0 then 1 else 0
    | cone P =>
      match n with
      | 0   => (P.faceCount 0) + 1
      | n+1 => P.faceCount n + P.faceCount (n+1)
    | prod P Q => ∑ i : Fin (n+1), (P.faceCount i.1) * (Q.faceCount (n-i.1))


  abbrev pointCount (P : PrismRepr) : Nat := P.faceCount 0
  abbrev edgeCount  (P : PrismRepr) : Nat := P.faceCount 1

  instance : Mul PrismRepr := ⟨λ P Q => P.prod Q⟩

  -- TODO: Clean this up, it is a bit of a mess
  def toString : PrismRepr → String
  | point => "•"
  -- | cone point => "—"
  -- | cone (cone point) => "⃤"
  -- | prod (cone point) (cone point) => "⃞"
  | cone (prod P Q) => s!"• ∧ ({(prod P Q).toString})"
  | cone P => s!"• ∧ {P.toString}"
  | prod (cone P) (cone Q) => s!"({(cone P).toString}) × ({(cone Q).toString})"
  | prod (cone P) Q => s!"({(cone P).toString}) × {Q.toString}"
  | prod (prod P₁ P₂) Q => s!"({(prod P₁ P₂).toString}) × {Q.toString}"
  | prod P (cone Q) => s!"{P.toString} × ({(cone Q).toString})"
  | prod P Q => s!"{P.toString} × {Q.toString}"

  instance : ToString PrismRepr := ⟨λ P => P.toString⟩

/-- Ordering of prism representations

  1. Prism representations are ordered by their dimensions.

  2. When the dimensions are the same:
    2a. `cone P` is always smaller then `prod Q₁ Q₂`.
    2b. For `prod P₁ P₂` and `prod Q₁ Q₂` we use lexicographical
      ordering of (P₁, P₂) and (Q₁, Q₂)
      i.e. we want: segment * square < square * segment
-/
  def ord (P Q : PrismRepr) : Ordering :=
    match P, Q with
    | point, point => .eq
    | point, _ => .lt
    | cone _, point => .gt
    | cone P, cone Q => ord P Q
    | cone P, prod _ _ =>
      if (cone P).dim ≤ Q.dim
      then .lt
      else .gt
    | prod _ _, point => .gt
    | prod P₁ P₂, cone Q =>
      if P₁.dim + P₂.dim < (cone Q).dim
      then .lt
      else .gt
    | prod P₁ P₂, prod Q₁ Q₂ =>
      match compare P.dim Q.dim with
      | .lt => .lt
      | .gt => .gt
      | .eq =>
        match ord P₁ Q₁ with
        | .lt => .lt
        | .gt => .gt
        | .eq => ord P₂ Q₂


  instance : LT PrismRepr := ⟨λ P Q => ord P Q = .lt⟩
  instance : LE PrismRepr := ⟨λ P Q => ord P Q ≠ .gt⟩

  local instance : DecidableEq Ordering :=
    λ x y =>
    match x, y with
    | .lt, .lt => isTrue (by rfl)
    | .gt, .gt => isTrue (by rfl)
    | .eq, .eq => isTrue (by rfl)
    | _, _ => isFalse (by sorry_proof)

  instance (P Q : PrismRepr) : Decidable (P < Q) :=
    if h : ord P Q = .lt then
      isTrue h
    else
      isFalse h

  instance (P Q : PrismRepr) : Decidable (P ≤ Q) :=
    if h : ord P Q = .gt then
      isFalse (by simp[LE.le]; assumption)
    else
      isTrue (by simp[LE.le]; assumption)


/-- PrismRepr is in canonical form iff
  1. it is a point
  2. it is a cone of a prism in canonical form
  3. is is a product of cone prisms
     (c P₁) × ... × (c Pₙ)
     the product is right associated, non-increasing and every prism is in canonical form
-/
  inductive IsCanonical : PrismRepr → Prop where
  | point : IsCanonical point
  | cone (P) (h : IsCanonical P) : IsCanonical (cone P)
  | cone_prod {P Q : PrismRepr} -- Product of two cones
      (hP : IsCanonical P) (hQ : IsCanonical Q) (hOrd : P ≤ Q)
      : IsCanonical (prod (cone P) (cone Q))
  | ord_prod {P Q S : PrismRepr} -- product has to be ordered and right associated
      (hP : IsCanonical P)
      (hCan : IsCanonical (prod (cone Q) S))
      (hOrd : P ≤ Q)
      : IsCanonical (prod (cone P) (prod (cone Q) S))


  instance isCanonical (P : PrismRepr) : Decidable (IsCanonical P) :=
    match P with
    | point => isTrue (.point)
    | cone P =>
      match isCanonical P with
      | isTrue h => isTrue (.cone P h)
      | isFalse h => isFalse (by intro q; cases q; rename_i q; apply (h q))
    | prod point Q => isFalse (by intro h; cases h)
    | prod (cone P) point => isFalse (by intro h; cases h)
    | prod (cone P) (cone Q) =>
      match isCanonical P, isCanonical Q with
      | isTrue hP, isTrue hQ =>
        if hOrd : P ≤ Q
        then isTrue (.cone_prod hP hQ hOrd)
        else isFalse (by intro h; cases h; rename_i h; apply (hOrd h))
      | isFalse hP, _ => isFalse (by intro h; cases h; rename_i h _ _; apply (hP h))
      | _, isFalse hQ => isFalse (by intro h; cases h; rename_i _ h _; apply (hQ h))
    | prod (cone P) (prod point S) => isFalse (by intro h; cases h)
    | prod (cone P) (prod (cone Q) S) =>
      match isCanonical P with
      | isTrue hP  =>
        if hOrd : P ≤ Q then
          match isCanonical (prod (cone Q) S) with
          | isTrue hCan => isTrue (.ord_prod hP hCan hOrd)
          | isFalse hCan => isFalse (by intro h; cases h; rename_i h; apply (hCan h))
        else
          isFalse (by intro h; cases h; rename_i _ h _; apply (hOrd h))
      | isFalse hP => isFalse (by intro h; cases h; rename_i h _ _ ; apply (hP h))
    | prod (cone P) (prod (prod Q₁ Q₂) S) => isFalse (by intro h; cases h)
    | prod (prod _ _) _ => isFalse (by intro h; cases h)

  -- TODO: Prove termination
  -- This should be a bubble sort, for termination have a look at:
  -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Termination.20of.20bubble.20sort
  def toCanonical : PrismRepr → PrismRepr
  | point => point
  | cone P => cone P.toCanonical
  | prod point P => P.toCanonical
  | prod (cone P) Q =>
    match Q.toCanonical with
    | point => cone P.toCanonical
    | cone Q =>
      let P := P.toCanonical
      if P ≤ Q
      then prod (cone P) (cone Q)
      else prod (cone Q) (cone P)
    | prod (cone Q₁) Q₂ =>
      if P ≤ Q₁
      then prod (cone P) (prod (cone Q₁) Q₂)
      else prod (cone Q₁) (prod (cone P) Q₂).toCanonical
    | prod _ _ => unreachable!
  | prod P Q =>
    match P.toCanonical with
    | point => Q.toCanonical
    | cone P => (prod (cone P) Q).toCanonical
    -- | prod (cone P₁) P₂ => (prod (cone P₁) (prod P₂ Q)) -- .toCanonical
    | prod P₁ P₂ => (prod P₁ (prod P₂ Q)).toCanonical
    -- | prod _ _ => unreachable!
  decreasing_by sorry_proof

  example : ((segment * segment) * segment |>.toCanonical )
            =
            (segment * (segment * segment ))
            := by native_decide -- by  rfl -- TODO: Make this provable by rfl!!!


  /-- toCanonical truly producees prism in canonical form -/
  @[simp]
  theorem toCanonical_IsCanonical (P : PrismRepr) : P.toCanonical.IsCanonical := sorry_proof
  /-- toCanonical preserves dimension -/
  @[simp]
  theorem toCanonical_dim (P : PrismRepr) : P.toCanonical.dim = P.dim := sorry_proof

  @[simp]
  theorem IsCanonical_point : point.IsCanonical := IsCanonical.point
  @[simp]
  theorem IsCanonical_base_of_cone (P : PrismRepr) (h : P.cone.IsCanonical) : P.IsCanonical := sorry_proof
  @[simp]
  theorem IsCanonical_cone (P : PrismRepr) (h : P.IsCanonical) : P.cone.IsCanonical := IsCanonical.cone P h
  @[simp]
  theorem IsCanonical_prod_fst (P Q : PrismRepr) (h : (P.prod Q).IsCanonical) : P.IsCanonical := sorry_proof
  @[simp]
  theorem IsCanonical_prod_snd (P Q : PrismRepr) (h : (P.prod Q).IsCanonical) : Q.IsCanonical := sorry_proof


  section ToCanonicalTests

    example : IsCanonical square := by native_decide
    example : ¬(prod point square).IsCanonical := by native_decide
    example : (prod point square).toCanonical = square := by native_decide

    example : ¬(prod triangle segment).IsCanonical := by native_decide
    example : (prod triangle segment).toCanonical = prism := by native_decide

    example : (prod (cone square) (cone triangle)).toCanonical
              =
              (prod (cone triangle) (cone square)) := by native_decide

  end ToCanonicalTests

end PrismRepr

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

  Retation to Semi-Semplicial sets
  --------------------------------

  This represents strictly increasing mapping from one Prism to another.

  TODO: expand on this
-/
inductive FaceRepr : Type where
  | point : FaceRepr
  | tip (P : PrismRepr) : FaceRepr
  | cone (f : FaceRepr) : FaceRepr
  | base (f : FaceRepr) : FaceRepr
  | prod (f g : FaceRepr)  : FaceRepr
with

  /-- Converts Face to Prism -/
  @[computed_field]
  toPrism : FaceRepr → PrismRepr
  | .point => .point
  | .tip _ => .point
  | .cone f => f.toPrism.cone
  | .base f => f.toPrism
  | .prod f g => f.toPrism.prod g.toPrism

  /-- Face `f` is a face of the prism `f.ofPrism` -/
  @[computed_field]
  ofPrism : FaceRepr → PrismRepr
  | .point => .point
  | .tip P => P.cone
  | .cone f => f.ofPrism.cone
  | .base f => f.ofPrism.cone
  | .prod f g => f.ofPrism.prod g.ofPrism
deriving DecidableEq, Inhabited

namespace FaceRepr

  def toString : FaceRepr → String
    | point => "•"
    | tip P => s!"(tip ({P}))"
    | cone f => s!"(cone {f.toString})"
    | base f => s!"(base {f.toString})"
    | prod f g => s!"({f.toString} × {g.toString})"

  instance : ToString FaceRepr := ⟨FaceRepr.toString⟩

  /-- Dimension of a face -/
  def dim (f : FaceRepr) : Nat := f.toPrism.dim

  /-- Isomorphism between faces of `P` and `P.toCanonical`.

  Maps every face of `P` to the corresponding face of the canonical `P.toCanonical`
  -/
  def toCanonical (f : FaceRepr) : FaceRepr :=
  match f with
  | .point => .point
  | .tip P => .tip P.toCanonical
  | .cone f => .cone f.toCanonical
  | .base f => .base f.toCanonical
  | .prod f g =>
    let f' := f.toCanonical
    match f' with
    | .point => g.toCanonical
    | .tip _ | .cone _ | .base _ =>
      let g' := g.toCanonical
      match g' with
      | .point => f'
      | .tip _ | .cone _ | .base _ =>
        if f'.ofPrism ≤ g'.ofPrism then .prod f' g' else .prod g' f'
      | .prod g₁' g₂' =>
        if f'.ofPrism ≤ g₁'.ofPrism
        then .prod f' (.prod g₁' g₂')
        else .prod g₁' (.prod f' g₂')
    | .prod f₁' f₂' =>
      let g' := (FaceRepr.prod f₂' g).toCanonical
      match g' with
      | .point => unreachable!
      | .tip _ | .cone _ | .base _ =>
        if f₁'.ofPrism ≤ g'.ofPrism then .prod f₁' g' else .prod g' f₁'
      | .prod g₁' g₂' =>
        if f₁'.ofPrism ≤ g₁'.ofPrism then .prod f₁' (.prod g₁' g₂') else .prod g₁' (.prod f₁' g₂')
  decreasing_by sorry_proof

  theorem toCanonical_ofPrism_IsCanonical (f : FaceRepr) : f.toCanonical.ofPrism.IsCanonical := sorry_proof
  theorem toCanonical_ofPrism (f : FaceRepr) : f.toCanonical.ofPrism = f.ofPrism.toCanonical := sorry_proof
  @[simp]
  theorem toCanonical_dim (f : FaceRepr) : f.toCanonical.dim = f.dim := sorry_proof

  /-- Isomorphism between faces of `P.toCanonical` and `P`.

  Maps every face of `P.toCanonical` to the corresponding face of `P`.

  It is an inverse of `FaceRepr.toCanonical` -/
  def fromCanonical (f : FaceRepr) (P : PrismRepr) (_ : f.ofPrism = P.toCanonical) : FaceRepr :=
  match P, f with
  | .point, .point => .point
  | .point, _ => unreachable!

  | .cone P, .tip _ => .tip P
  | .cone P, .cone f' => .cone (f'.fromCanonical P sorry_proof)
  | .cone P, .base f' => .base (f'.fromCanonical P sorry_proof)
  | .cone _, _ => unreachable!

  | .prod .point P', f' =>
    FaceRepr.prod .point (f'.fromCanonical P' sorry_proof)

  | .prod (.cone P) Q, f' =>
    let Q' := Q.toCanonical
    match Q' with
    | .point =>
      .prod (f'.fromCanonical (.cone P) sorry_proof)
            (FaceRepr.point.fromCanonical Q sorry_proof)

    | .cone Q' =>
      match f' with
      | .prod f' g' =>
        let P' := P.toCanonical
        if P' ≤ Q' then
          .prod (f'.fromCanonical (.cone P) sorry_proof) (g'.fromCanonical Q sorry_proof)
        else
          .prod (g'.fromCanonical (.cone P) sorry_proof) (f'.fromCanonical Q sorry_proof)
      | _ => unreachable!

    | .prod (.cone Q₁') Q₂' =>
      match f' with
      | .prod f' g' =>
        let P' := P.toCanonical
        if P' ≤ Q₁' then
          .prod (f'.fromCanonical P.cone sorry_proof) (g'.fromCanonical Q sorry_proof)
        else
          let f'' := (f'.fromCanonical Q₁'.cone sorry_proof)
          let g'' := (g'.fromCanonical (.prod P.cone Q₂') sorry_proof)
          match g'' with
          | .prod g₁''' g₂''' =>
            .prod g₁''' ((FaceRepr.prod f'' g₂''').fromCanonical Q sorry_proof)
          | _ => unreachable!
      | _ => unreachable!
    | _ => unreachable!
  | .prod P Q, fg =>
    let P' := P.toCanonical
    match P' with
    | .point =>
      .prod (FaceRepr.point.fromCanonical P sorry_proof) (fg.fromCanonical Q sorry_proof)
    | .cone P' =>
      let fg' := fg.fromCanonical (.prod P'.cone Q) sorry_proof
      match fg' with
      | .prod f' g' => .prod (f'.fromCanonical P sorry_proof) g'
      | _ => unreachable!
    | .prod (.cone P₁') P₂' =>
        let fg' := fg.fromCanonical (.prod P₁'.cone (.prod P₂' Q)) sorry_proof
        match fg' with
        | .prod f₁' (.prod f₂' g') =>
          .prod ((FaceRepr.prod f₁' f₂').fromCanonical P sorry_proof) g'
        | _ => unreachable!
    | _ => unreachable!
  decreasing_by sorry_proof

  @[simp]
  theorem fromCanonical_ofPrism (f : FaceRepr) (P : PrismRepr) (h : f.ofPrism = P.toCanonical)
    : (fromCanonical f P h).ofPrism = P
  := sorry_proof

  @[simp]
  theorem fromCanonical_toPrism (f : FaceRepr) (P : PrismRepr) (h : f.ofPrism = P.toCanonical)
    : (fromCanonical f P h).toPrism.toCanonical = f.toPrism.toCanonical
  := sorry_proof

  @[simp]
  theorem fromCanonical_dim (f : FaceRepr) (P : PrismRepr) (h : f.ofPrism = P.toCanonical)
    : (fromCanonical f P h).dim = f.dim
  := sorry_proof

  @[simp]
  theorem ofPrism_toCanonical_toCanonical_ofPrism (f : FaceRepr)
    : f.toCanonical.ofPrism = f.ofPrism.toCanonical
  := sorry_proof

  @[simp]
  theorem toPrism_toCanonical_toCanonical_toPrism (f : FaceRepr)
    : f.toCanonical.toPrism.toCanonical = f.toPrism.toCanonical
  := sorry_proof

/--
Face of a face is a face. If we have a face `f` of prism `P` and a face `g` of prism `f.toPrism` then `g` is also a face of `P`.

It is a called "comp" because we can think of `f` and `g` as inclusions of a prism to a larger prism. Reinterpreting `g` as a face of `P` is just a composition of these inclusions.


---

Categorical perspective
-----------------------
This is morphism composition. The face `f` is a morphism `Q → P` and `g` is a morphism `S → Q` in `Prism` category, `comp f g : Face P` is just their composition.
-/

  def comp (f g : FaceRepr)
    (h : f.toPrism = g.ofPrism := by (first | rfl |simp))
    : FaceRepr
    :=
      match f, g, h with
      |   point,   point, _ => point
      |  tip P',   point, _ => tip P'
      | cone f',   tip _, _ => tip f'.ofPrism
      | cone f', cone g', _ =>
        cone (f'.comp g' (sorry_proof))
      | cone f', base g', _ =>
        base (f'.comp g' (sorry_proof))
      | base f',      g', _ =>
        base (f'.comp g' (sorry_proof))
      | prod f' f'', prod g' g'', _ =>
        prod (f'.comp g'   (sorry_proof))
             (f''.comp g'' (sorry_proof))


    /-- The prism type of a face does not depend on the larger prism. -/
    @[simp]
    theorem comp_toPrism (f g : FaceRepr) (h)
      : (f.comp g h).toPrism = g.toPrism
      := sorry_proof

    /--  -/
    @[simp]
    theorem comp_ofPrism (f g : FaceRepr) (h)
      : (f.comp g h).ofPrism = f.ofPrism
      := sorry_proof

    /-- The dimension of a face does not depend on the larger prism. -/
    @[simp]
    theorem comp_dim (f g : FaceRepr) (h)
      : (f.comp g h).dim = g.dim
      := sorry_proof

end FaceRepr

namespace PrismRepr

  /-- Returns prism `P` is its own face, i.e. the face with the highest dimension. -/
  def topFace : PrismRepr → FaceRepr
  | .point => .point
  | .cone P => .cone P.topFace
  | .prod P Q => .prod P.topFace Q.topFace

  @[simp]
  theorem topFace_ofPrism (P : PrismRepr) : P.topFace.ofPrism = P := sorry_proof
  @[simp]
  theorem topFace_toPrism (P : PrismRepr) : P.topFace.toPrism = P := sorry_proof

  /-- The first `n`-face of `P` -/
  def first (P : PrismRepr) (n : Nat) : Option FaceRepr:=
    match P, n with
    | .point, 0 => some .point
    | .point, _ => none
    | .cone P', 0 => some $ .tip P'
    | .cone P', n'+1 =>
      match P'.first n' with
      | some f => some $ .cone f
      | none => none
    | .prod P' Q', n =>
      Id.run do
      for i in [0:n+1] do
        match P'.first i, Q'.first (n-i) with
        | some f', some g' =>
          return some $ .prod f' g'
        | _, _ => continue
      none

  theorem first_ofPrism (P : PrismRepr) (n : Nat)
    : match P.first n with
      | some f => f.ofPrism = P
      | none => True
    := sorry_proof

  theorem first_dim (P : PrismRepr) (n : Nat)
    : match P.first n with
      | some f => f.dim = n
      | none => True
    := sorry_proof

  def prodSplit (P : PrismRepr) : List PrismRepr :=
  match P with
  | .point  => [.point]
  | .cone Q => [.cone Q]
  | .prod Q₁ Q₂ => Q₁ :: Q₂.prodSplit

  def prodHead (P : PrismRepr) : PrismRepr :=
  match P with
  | .point  => .point
  | .cone Q => .cone Q
  | .prod Q₁ _ => Q₁

  def prodTail (P : PrismRepr) : PrismRepr :=
  match P with
  | .point  => .point
  | .cone _ => .point
  | .prod _ Q₂ => Q₂

  -- def first' (P : PrismRepr) (n : Option Nat := none) : Option (FaceRepr' P n) :=
  --   match n with
  --   | some n => P.first n |>.map (⟨·, sorry_proof, sorry_proof⟩)
  --   | none     => P.first 0   |>.map (⟨·, sorry_proof, sorry_proof⟩)

end PrismRepr

namespace FaceRepr

  /-- Next face of the same Prism and dimension -/
  def next (f : FaceRepr) : Option FaceRepr :=
    match f.ofPrism, f.dim, f with
    | .point, 0, point => none
    | .cone P', 0, tip _ =>
      match P'.first 0 with
      | some f' => some $ base f'
      | none => none
    | .cone P', n'+1, cone f' =>
      match next f' with
      | some f'' => some $ cone f''
      | none =>
        match P'.first (n'+1) with
        | some f'' => some $ base f''
        | none => none
    | .cone _, _, base f' =>
      match next f' with
      | some f'' => some $ base f''
      | none => none
    | _, _, prod f' g' =>
      let P' := f'.ofPrism
      let Q' := g'.ofPrism
      match next f' with
      | some f'' => some $ prod f'' g'
      | none =>
        match P'.first f'.dim, next g' with
        | some f'', some g'' => some $ .prod f'' g''
        | _, _ =>
          match g'.dim with
          | 0 => none
          | m''+1 =>
            match P'.first (f'.dim+1), Q'.first m'' with
            | some f'', some g'' => some $ .prod f'' g''
            | _, _ => none
    | _, _, _ => panic! "Unreachable code in Face.next. This is a bug!"

  theorem next_ofPrism (f : FaceRepr)
    : match f.next with
      | some f' => f'.ofPrism = f.ofPrism
      | none => True
    := sorry_proof

  theorem next_dim (f : FaceRepr)
    : match f.next with
      | some f' => f'.dim = f.dim
      | none => True
    := sorry_proof

end FaceRepr

-- Next face of the same prism and if dimension is specified then of the
--   same dimension as well
-- def FaceRepr'.next {P : PrismRepr} {n : Option Nat}  -- Note that `P` is not Option!
--   (f : FaceRepr' (some P) n) : Option (FaceRepr' P n) :=
--   match f.1.next, f.1.next_ofPrism, f.1.next_dim with
--   | some f', h, q => some ⟨f', by rw [f.2] at h; assumption; done,
--                                by cases n; simp; rename_i n; rw [f.3] at q; assumption; done⟩
--   | none, _, _ => -- Out of faces of the same prism and dimension
--     match n with
--     | some _ => none
--     | none =>  -- if dimension is not specified get a face of higher dimension
--       match f.1.ofPrism.first (f.1.dim+1) with
--       | some f => some ⟨f, sorry_proof, sorry_proof⟩
--       | none => none


-- instance (P : PrismRepr) (n : Option Nat)
--   : Iterable (FaceRepr' P n) :=
-- {
--   first := P.first' n
--   next := λ f => f.next
--   decEq := by infer_instance
-- }

-- /-- All faces of a prism, optionaly all faces with of specified dimension -/
-- def PrismRepr.faces (P : PrismRepr) (n : Option Nat := none) := Iterable.fullRange (FaceRepr' P n)
-- /-- All faces of a face, optionaly all faces with of specified dimension -/
-- def FaceRepr.faces  (f : FaceRepr)  (n : Option Nat := none) := Iterable.fullRange (FaceRepr' f.toPrism n)
-- /-- All faces of a face, optionaly all faces with of specified dimension -/
-- def FaceRepr'.faces (f : FaceRepr' P n') (n : Option Nat := none)  := f.1.faces n

-- abbrev PrismRepr.Point (P : PrismRepr) : Type := FaceRepr' P (some 0)
-- abbrev PrismRepr.Edge  (P : PrismRepr) : Type := FaceRepr' P (some 0)

-- /-- All points of a prism -/
-- abbrev PrismRepr.points (P : PrismRepr) := Iterable.fullRange (FaceRepr' P (some 0))
-- /-- All edges of a prism -/
-- abbrev PrismRepr.edges (P : PrismRepr) := Iterable.fullRange (FaceRepr' P (some 1))

-- /-- All points of a face -/
-- abbrev FaceRepr.points (f : FaceRepr) := Iterable.fullRange (FaceRepr' f.toPrism (some 0))
-- /-- All edges of a face -/
-- abbrev FaceRepr.edges (f : FaceRepr) := Iterable.fullRange (FaceRepr' f.toPrism (some 1))

-- /-- All points of a face -/
-- abbrev FaceRepr'.points (f : FaceRepr' P n') := f.1.faces (some 0)
-- /-- All edges of a face -/
-- abbrev FaceRepr'.edges (f : FaceRepr' P n') := f.1.faces (some 1)


/-- Index of a face among all faces of the same prism and dimension -/
-- def FaceRepr.index (f : FaceRepr) : Nat :=
--   match f.dim, f with
--   | _, point => 0
--   | _, tip _ => 0
--   | _, cone f' => f'.index
--   | 0, base f' => f'.index + 1
--   | n'+1, base f' => f'.ofPrism.faceCount n' + f'.index
--   | _, prod f' g' =>
--     let P' := f'.ofPrism
--     let Q' := g'.ofPrism
--     (∑ i : Fin f'.dim, (P'.faceCount i)*(Q'.faceCount (f.dim-i)))
--     + g'.index * (P'.faceCount f'.dim)
--     + f'.index

def FaceRepr.index (f : FaceRepr) : Nat :=
  match f with
  | point => 0
  | tip P => P.faceCount 0
  | base f' => f'.index
  | cone f' => (f'.ofPrism.faceCount f.dim) + f'.index
  | prod f' g' =>
    let P' := f'.ofPrism
    let Q' := g'.ofPrism
    (∑ i : Fin f'.dim, (P'.faceCount i)*(Q'.faceCount (f.dim-i)))
    + g'.index * (P'.faceCount f'.dim)
    + f'.index


def FaceRepr.fromIndex (P : PrismRepr) (dim : Nat) (i : Fin (P.faceCount dim)) : FaceRepr :=
  match P, dim with
  | .point, 0 => point
  | .cone P', 0 =>
    let n' := P'.faceCount 0
    if h : i.1 < n' then
      .base (fromIndex P' 0 ⟨i.1, h⟩)
    else
      .tip P'
  | .cone P', dim'+1 =>
    let n' := P'.faceCount (dim'+1)
    if h : i.1 < n' then
      .base (fromIndex P' (dim'+1) ⟨i.1, h⟩)
    else
      .cone (fromIndex P' dim' ⟨i.1 - n', sorry_proof⟩)
  | .prod P' Q', _ => Id.run do
    let mut n := 0
    for d' in [0:dim+1] do
      let Δn := (P'.faceCount d') * (Q'.faceCount (dim-d'))
      if h : i.1 < n + Δn then
        let iP := (i-n) % (P'.faceCount d')
        let iQ := (i-n) / (P'.faceCount d')
        return (fromIndex P' d' ⟨iP,sorry_proof⟩).prod (fromIndex Q' (dim-d') ⟨iQ,sorry_proof⟩)
      else
        n := n + Δn

    panic! s!"Invalid index {i} in FaceRepr.fromIndex!"

/-- Index of a face is smaller then the number of faces of the same dimesnsion and of the same Prism -/
def FaceRepr.index_numberOfFaces (f : FaceRepr)
  : f.index < f.ofPrism.faceCount f.dim
  := sorry_proof

/-- Face is uniquelly determined by its parent prism, dimension and index -/
def FaceRepr.index_ext (f g : FaceRepr)
  : f.ofPrism = g.ofPrism → f.dim = g.dim → f.index = g.index → f = g
  := sorry_proof

abbrev PrismRepr.Space : PrismRepr → Type
| .point => Unit
| .cone P => ℝ × P.Space
-- TODO: Make sure that the space of an edge is just ℝ
-- | .cone .point => ℝ
-- | .cone (.cone P) => ℝ × (PrismRepr.cone P).Space
-- | .cone (.prod P) => ℝ × (PrismRepr.cone P).Space
| .prod P Q => P.Space × Q.Space

-- abbrev PrismRepr.Space' : PrismRepr → Type
-- | .point => Unit
-- | .cone .point => ℝ
-- | .cone P => ℝ × P.Space
-- | .prod P Q => P.Space × Q.Space

instance PrismRepr.instVecSpace (P : PrismRepr) : Vec P.Space :=
  match P with
  | point =>    by simp[Space]; infer_instance; done
  | cone .point => by simp[Space]; infer_instance; done
  | cone P =>   by simp[Space]; apply (@instVecProd _ _ (by infer_instance) (instVecSpace P)); done
  | prod P Q => by simp[Space]; apply (@instVecProd _ _ (instVecSpace P) (instVecSpace Q)); done

instance PrismRepr.Space.toString {P : PrismRepr} (x : P.Space) : String :=
  match P, x with
  | .point, _ => "()"
  | .cone _, (t, x) => s!"({t},{x.toString})"
  | .prod _ _, (x, y) => s!"({x.toString},{y.toString})"

instance {P : PrismRepr} : ToString P.Space := ⟨λ x => x.toString⟩

/-- Space of a face, it is the same as the space of the corresponding prism -/
abbrev FaceRepr.Space (f : FaceRepr) : Type := f.toPrism.Space

/-- For a point `x` in the coordinates of a face `f` give coordinates of `x` w.r.t the the parent prism `f.ofPrism`
-/
def FaceRepr.embed (f : FaceRepr) (x : f.Space) : f.ofPrism.Space :=
match f, x with
| .point, _ => ()
| .tip _x, _ => (1,0)
| .cone P', x'' =>
  let (t', x') := x''
  (t', (1-t')•(P'.embed x'))
| .base P', x'' =>
  (0, (P'.embed x''))
| .prod P' Q', x'' =>
  let (x', y') := x''
  (P'.embed x', Q'.embed y')

-- def FaceRepr'.embed (f : FaceRepr' (some P) n) (x : f.toPrism.Space) : P.Space := f.2 ▸ (f.1.embed x)
def PrismRepr.barycenter (P : PrismRepr) : P.Space :=
  match P with
  | point => 0
  | cone P' =>
    let w := (1.0 : ℝ)/(P.pointCount : ℝ)
    (w, (1-w)•P'.barycenter)
  | prod P Q =>
    (P.barycenter, Q.barycenter)

  -- def toRn : {P : Prism} → P.E → ℝ^P.dim := sorry_proof
  -- def fromRn : {P : Prism} → ℝ^P.dim → P.E := sorry_proof


/-- Barycentric coordinates of a prism

    This implementation has bad numerical properties and it is thus serves mostly as a specification -/
def PrismRepr.barycentricCoordSpec {P : PrismRepr} (p : FaceRepr) (_ : p.ofPrism = P ∧ p.dim = 0 /- `p` is a point of P -/) (x : P.Space) : ℝ :=
  match P, p, x with
  | .point, _, _ => 1
  | .cone _, .tip _, (t, _) => t
  | .cone _, .base p', (t, x') =>
    (1-t) * (barycentricCoordSpec p' sorry_proof ((1/(1-t)) • x'))
  | .prod _ _, .prod p q, (x, y) =>
    (barycentricCoordSpec p sorry_proof x) *
    (barycentricCoordSpec q sorry_proof y)
  | .cone _, .cone _, _ => unreachable!


-- Most likely this has bad numerics!!!
-- What type of barycentric coordinates are these? They are not harmonic, maybe Wachspress?
-- Can we define different set of coordinates inductively?
def PrismRepr.barycentricCoord {P : PrismRepr} (p : FaceRepr) (h : p.ofPrism = P ∧ p.dim = 0 /- `p` is a point of P -/) (x : P.Space) : ℝ :=
  match P, p, x, h.1 with
  | .point, _, _, _ => 1
  | .cone .point, .base _, (t, ()), _ => 1-t
  | .cone _, .tip _, (t, (_)), _ => t
  | .cone (.cone _), .base (.tip _), (_, (s, _)), _ => s
  | .cone (.cone P), .base (.base p), (t, (s, x)), _ =>
    -- let p' : FaceRepr' (some $ .cone P) (0 : Nat) := ⟨.base p, sorry_proof, sorry_proof⟩
    barycentricCoord (P := P.cone) (.base p) sorry_proof (t+s, x)
  | .cone (.prod P Q), .base (.prod p q), (t, (x, y)),_ =>
    -- let p' : FaceRepr' (some $ .cone P) (0 : Nat) := ⟨.base p, sorry_proof, sorry_proof⟩
    (barycentricCoord (P := P.cone) (.base p) sorry_proof (t,x)) *
    (barycentricCoord q sorry_proof ((1/(1-t)) • y))
  | .prod _ _, .prod p q, (x, y), _ =>
    (barycentricCoord p sorry_proof x) *
    (barycentricCoord q sorry_proof y)
  -- In all these cases `p` is not a point
  -- Can we modify the original match statement to eliminate these?
  -- | .cone (.prod _ _), .cone _, _ => unreachable!
  -- | .cone (.cone _),  .base (.cone _), _ => unreachable!
  -- | .cone (.cone _),  .cone _, _ => unreachable!
  -- | .cone .point, .cone _, _ => unreachable!


-- Not all indices are valid
-- in particular `.prod p q` then p and q have to have the same degree!
inductive BasisIndex where
  | point (n : Nat) : BasisIndex
  | cone  (n : Nat) (b : BasisIndex) : BasisIndex
  | prod (p q : BasisIndex) : BasisIndex

-- index with degree, but it is difficult to work with
inductive BasisIndex' : Nat → Type where
  | point (n : Nat) : BasisIndex' n
  | cone  (n : Nat) (b : BasisIndex' m) : BasisIndex' (n+m)
  | prod (p q : BasisIndex' n) : BasisIndex' n

def BasisIndex.ofPrism (i : BasisIndex) : PrismRepr :=
  match i with
  | point _ => .point
  | cone _ p => .cone p.ofPrism
  | prod p q => .prod p.ofPrism q.ofPrism

def BasisIndex.degree (i : BasisIndex) : Nat :=
  match i with
  | point n => n
  | cone n p => n + p.degree
  | prod p q => max p.degree q.degree -- if p.degree ≠ q.degree then it is not a valid index!!!


-- Lagrangian basis functions implementation
private def BasisIndex.evalImpl (idx : BasisIndex) (deg : Nat) (x : idx.ofPrism.Space) : ℝ :=
  match idx, x with
  | .point _, _ => 1

  | .cone n (.point m), (t, _) =>
          (∏ i : Fin m, (1 - t - i / deg) / ((m:ℝ)/deg - (i:ℝ) / deg)) *
          (∏ j : Fin n, (    t - j / deg) / ((n:ℝ)/deg - (j:ℝ) / deg))

  | .cone n (.cone m p), (t, s, x) =>
          (∏ i : Fin n, (t - i / deg) / ((n:ℝ)  / deg - (i:ℝ) / deg)) *
          (∏ i : Fin m, (s - i / deg) / ((m:ℝ) / deg - (i:ℝ) / deg)) *
          ((BasisIndex.cone 0 p).evalImpl deg (t+s, x))

  | .cone n (.prod p q), (t, (x,y)) =>
          ((BasisIndex.cone n p).evalImpl deg (t, x)) *
          ((BasisIndex.cone n q).evalImpl deg (t, y)) /
          (∏ i : Fin n, (t - i / deg) / ((n:ℝ) / deg - i / deg))

  | .prod p q, (x, y) => (p.evalImpl deg x) * (q.evalImpl deg y)


-- Lagrangian basis function correspoinding to the index `idx`
def BasisIndex.eval (idx : BasisIndex) (x : idx.ofPrism.Space) : ℝ :=
  idx.evalImpl idx.degree x


-- Lagrangian node correspoinding to the index `idx`
def BasisIndex.node (idx : BasisIndex) : idx.ofPrism.Space :=
  match idx with
  | .point _ => ()
  | .cone n p => let deg := n + p.degree; ((n:ℝ)/deg, ((p.degree:ℝ)/deg) • p.node)
  | .prod p q => (p.node, q.node)


/-- Index specifying Lagrangian basis function -/
inductive LagrangianIndex : (P : PrismRepr) → (deg : Nat) → Type
  | point (n : Nat) : LagrangianIndex .point n
  | cone (n : Nat) (p : LagrangianIndex P m) : LagrangianIndex (.cone P) (n+m)
  | prod (p : LagrangianIndex P n) (q : LagrangianIndex Q n) : LagrangianIndex (.prod P Q) n

def LagrangianIndex.toBasisIndex : LagrangianIndex P deg → BasisIndex
| .point n  => .point n
| .cone n p => .cone n p.toBasisIndex
| .prod p q => .prod p.toBasisIndex q.toBasisIndex


theorem LagrangianIndex.toBasisIndex_ofPrism (idx : LagrangianIndex P deg)
  : idx.toBasisIndex.ofPrism = P :=
by induction idx <;> repeat (first | assumption | constructor | simp[BasisIndex.ofPrism, toBasisIndex])

theorem LagrangianIndex.toBasisIndex_degree (idx : LagrangianIndex P deg)
  : idx.toBasisIndex.degree = deg :=
by
  induction idx <;> repeat (first | assumption | constructor | simp[BasisIndex.degree, toBasisIndex] | aesop)

def LagrangianIndex.node (idx : LagrangianIndex P deg) : P.Space := (idx.toBasisIndex_ofPrism ▸ idx.toBasisIndex.node)

#eval show IO Unit from do
  let idx := BasisIndex.cone 0 (BasisIndex.point 1)
  IO.println (idx.eval (0,()))
  IO.println (idx.eval (0.4,()))
  IO.println (idx.eval (1,()))
  let P : ℝ × Unit := idx.node
  IO.println P

#eval show IO Unit from do
  let idx := BasisIndex.cone 1 (BasisIndex.point 1)
  IO.println (idx.eval (0,()))
  IO.println (idx.eval (0.5,()))
  IO.println (idx.eval (1,()))
  let P : ℝ × Unit := idx.node
  IO.println P


#eval show IO Unit from do
  let idx := BasisIndex.cone 1 (BasisIndex.cone 2 (BasisIndex.point 0))
  IO.println (idx.eval (0,0,()))
  IO.println (idx.eval (0,1,()))
  IO.println (idx.eval (1,0,()))
  IO.println (idx.eval (0.5,0.5,()))
  IO.println (idx.eval (1/3,1/3,()))
  IO.println (idx.eval (1/3,2/3,()))
  IO.println (idx.eval (2/3,1/3,()))
  IO.println (idx.eval (1/3,0,()))
  IO.println (idx.eval (0,1/3,()))
  IO.println (idx.eval (2/3,0,()))
  let P : ℝ × ℝ × Unit := idx.node
  IO.println P


#eval show IO Unit from do
  let idx := (BasisIndex.prod (.cone 1 (.point 0)) (.cone 0 (.point 1)))
  IO.println (idx.eval ((0,()),(0,())))
  IO.println (idx.eval ((1,()),(0,())))
  IO.println (idx.eval ((0,()),(1,())))
  IO.println (idx.eval ((1,()),(1,())))
  let P : (ℝ × Unit) × (ℝ × Unit) := idx.node
  IO.println P


#eval show IO Unit from do
  let idx := BasisIndex.cone 0 (.prod (.cone 1 (.point 1)) (.cone 1 (.point 1)))
  IO.println (idx.eval (0,((0,()),(0,()))))
  IO.println (idx.eval (0,((1,()),(0,()))))
  IO.println (idx.eval (0,((0,()),(1,()))))
  IO.println (idx.eval (0,((1,()),(1,()))))
  IO.println (idx.eval (1,((0,()),(0,()))))
  IO.println (idx.eval (0,((0.5,()),(0.5,()))))
  IO.println (idx.eval (0.5,((0.5,()),(0.5,()))))
  IO.println (idx.eval (0.5,((0.0,()),(0.5,()))))
  let P : ℝ × (ℝ × Unit) × (ℝ × Unit) := idx.node
  IO.println P


#eval show IO Unit from do
  let idx := BasisIndex.cone 1 (.prod (.cone 1 (.point 0)) (.cone 1 (.point 0)))
  IO.println (idx.eval (0,((0,()),(0,()))))
  IO.println (idx.eval (0,((1,()),(0,()))))
  IO.println (idx.eval (0,((0,()),(1,()))))
  IO.println (idx.eval (0,((1,()),(1,()))))
  IO.println (idx.eval (1,((0,()),(0,()))))
  IO.println (idx.eval (0,((0.5,()),(0.5,()))))
  IO.println (idx.eval (0.5,((0.5,()),(0.5,()))))
  IO.println (idx.eval (0.5,((0.0,()),(0.5,()))))
  IO.println (idx.eval (0,((0.5,()),(0,()))))
  IO.println (idx.eval (0,((0.0,()),(0.5,()))))
  let P : ℝ × (ℝ × Unit) × (ℝ × Unit) := idx.node
  IO.println P


theorem PrismRepr.barycentricCoord_sound {P : PrismRepr} (p : FaceRepr) (h : p.ofPrism = P ∧ p.dim = 0 /- `p` is a point of P -/) (x : P.Space)
  : P.barycentricCoord p h x = P.barycentricCoordSpec p h x := sorry_proof

namespace PrismRepr

end PrismRepr

  #eval triangle < square
  #eval triangle * triangle
  #eval segment * pyramid |>.dim

  -- Ordering of 4D prisms
  -- cone of 3D
  #eval tet.cone < pyramid.cone
  #eval pyramid.cone < prism.cone
  #eval prism.cone < cube.cone
  #eval cube.cone < segment * tet
  -- 1D × 3D
  #eval segment * tet < segment * pyramid
  #eval segment * pyramid < segment * prism
  -- 1D × 1D × 2D
  #eval segment * prism < segment * cube
  -- 1D × 1D × 1D × 1D
  #eval segment * cube < triangle * triangle


-- order preserving map from one prism to another prism
-- Should include pure inclusions like Face but also collapses
--
-- There is some non-uniqueness, doing `shift` if the same as `cone ∘ base`
-- inductive Morph : Prism → Types
--   | point : Morph point
--   | tip (P : Prism) : Morph (cone P)
--   | cone {P : Prism} (f : Morph P) : Morph (cone P)
--   | base {P : Prism} (f : Morph P) : Morph (cone P)
--   | collapse {P : Prism} (m : Morph (cone P)) : Morph (cone (cone P))
--   | shift    {P : Prism} (m : Morph (cone P)) : Morph (cone (cone P))
--   | prod {P Q : Prism} (f : Morph P) (g : Morph Q) : Morph (prod P Q)

-- Face if Morph not containing collapses and shifts


#exit
-- structure Inclusion (Q P : Prism) where
--   f  : Face P
--   hq : f.toPrism = Q


-- instance (Q P) : CoeFun (Inclusion Q P) (λ a => Face Q → Face P) := sorry

-- variable (ι : Inclusion Q P) (f : Face Q)

-- #check (ι f)




  -- For finite element spaces look at:
  --
  -- Construction of scalar and vector finite element families on polygonal and polyhedral meshes
  --   https://arxiv.org/abs/1405.6978
  --
  -- Minimal degree H(curl) And H(div) conforming finite elements on polytopal meshes
  --   https://arxiv.org/abs/1502.01553



private def testBarycentricCoord (P : PrismRepr) : IO Unit := do
  IO.println s!"Testing barycentric coordinates of {P}"

  for pi in P.points do
    for pj in P.points do
      IO.print s!"{P.coord pi (pj.embed 0)} "

    IO.println ""
  IO.println ""

#eval testBarycentricCoord segment
#eval testBarycentricCoord cube.cone
#eval testBarycentricCoord pyramid.cone





def analyzePrism (P : PrismRepr) : IO Unit := do
  IO.println s!"Analyzing {P}"

  for d in [0:P.dim+1] do
    IO.println s!"  Looking at {d}-faces"

    for f in P.faces d do
      IO.println s!"     dim: {f.1.dim} | id: {f.1.index} | {f.1} | {f.1.toPrism} | {f.1.toPrism.toCanonical} | {f.toCanonical.fromCanonical == f} "
      IO.print   s!"       "
      for g in f.faces do
        IO.print s!"| {g.1.ofPrism} "
      IO.println ""

      -- IO.print s!"       "
      -- for g in f.1.faces do
      --   IO.print s!"| {g.toPrism.toCanonical} "
      -- IO.println s!""

      -- let mut f := Face.first P d |>.getD default
      -- for i in [0:P.faceCount d] do

      --   IO.println s!"    face {i}: id:{f.toFin} | {f.toPrism} | {f.toPrism.toCanonical} | canonical: {f == f}"

      --   f.toPrism.forFacesM
      --     λ g => IO.println s!"     {g.toPrism == (f.comp g |>.toPrism)}"-- g.toPrism.forFacesM

      --   f.toCanonical.toPrism.forFacesM
      --     λ g => IO.println s!"     {g.toCanonical.fromCanonical == g}"-- g.toPrism.forFacesM

      --   --     λ h =>
      --   --       let h'  := Face.ofFace h
      --   --       let h'' := Face.ofFace h'
      --   --       IO.println s!"{h''}"
      --   -- -- IO.println ""
      --   f := f.next.getD default



#eval analyzePrism triangle
#eval analyzePrism (PrismRepr.point.prod (square.prod .point))
#eval analyzePrism pyramid
#eval analyzePrism (triangle.prod segment)
#eval ((cube).cone.prod triangle).dim
