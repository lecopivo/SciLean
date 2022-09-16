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
inductive Prism.Repr where
  | point : Prism.Repr
  | cone (P : Prism.Repr) : Prism.Repr
  | prod (P Q : Prism.Repr) : Prism.Repr
deriving DecidableEq, Inhabited

namespace Prism

  /-- Number of prisms of given dimension -/
  def count (dim : Nat) : Nat :=
    match dim with
    | 0 => 1
    | (n+1) => (n + 1)

end Prism

#check ℕ × (ℕ × ℕ)

namespace Prism.Repr

  -- TODO: prove termination
  partial def listProd : List Prism.Repr → Prism.Repr
  | [] => point
  | [P] => P
  | P::Q::Ps => listProd ((prod P Q)::Ps)

  /-- Dimension of a prism -/
  def dim : (P : Prism.Repr) → Nat
    | point => 0
    | cone P' => 1 + P'.dim
    | prod P' Q' => P'.dim + Q'.dim


/-- Ordering of prism representations 

  1. Prism representations are ordered by their dimensions.

  2. When the dimensions are the same:
    2a. `cone P` is always smaller then `prod Q₁ Q₂`.
    2b. For `prod P₁ P₂` and `prod Q₁ Q₂` we use lexicographical
      ordering of (P₁, P₂) and (Q₁, Q₂)
      i.e. we want: segment * square < square * segment

-/
  def ord (P Q : Prism.Repr) : Ordering :=
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

      
  instance : LT Prism.Repr := ⟨λ P Q => ord P Q = .lt⟩
  instance : LE Prism.Repr := ⟨λ P Q => ord P Q ≠ .gt⟩

  instance : DecidableEq Ordering := 
    λ x y => 
    match x, y with
    | .lt, .lt => isTrue (by rfl)
    | .gt, .gt => isTrue (by rfl)
    | .eq, .eq => isTrue (by rfl)
    | _, _ => isFalse (by sorry_proof)
     
  instance (P Q : Prism.Repr) : Decidable (P < Q) := 
    if h : ord P Q = .lt then
      isTrue h
    else 
      isFalse h

  instance (P Q : Prism.Repr) : Decidable (P ≤ Q) := 
    if h : ord P Q = .gt then
      isFalse (by simp[LE.le]; assumption)
    else 
      isTrue (by simp[LE.le]; assumption)


  def segment  := cone point
  def triangle := cone segment
  def square   := prod segment segment
  def tet      := cone triangle
  def cube     := prod segment square
  def cube'    := prod square segment
  def pyramid  := cone square
  def prism    := prod segment triangle
  def prism'   := prod triangle segment

  /-
  #eval segment < triangle
  #eval triangle < square
  #eval square < cube
  #eval cube < cube'
  #eval prism < prism'

  #eval square < tet
  #eval triangle < tet
  #eval triangle < cube
  #eval cube < prod (prod point segment) square

  #eval tet < pyramid
  #eval pyramid < prism
  #eval prism < cube
  #eval tet < prism
  #eval tet < cube
  -/

/-- Prism.Repr is in canonical form iff
  1. it is a point
  2. it is a cone of a prism in canonical form
  3. is is a product of cone prisms
     (c P₁) × ... × (c Pₙ) 
     the product is right associated, non-increasing and every prism is in canonical form

-/
  inductive IsCanonical : Prism.Repr → Prop where
  | point : IsCanonical point
  | cone (P) (h : IsCanonical P) : IsCanonical (cone P)

  -- | prod (Ps : List Prism.Repr) 
  --        (allIsCanonical : ∀ i, IsCanonical (Ps.get i)) 
  --        (ordered : Ps.isSorted (λ P Q => P.id ≤ Q.id)) 
  --        : IsCanonical (listProd (Ps.map (·.cone)))

  -- Are these two this equivalent to the above? 
  -- Product of two cones
  | cone_prod {P Q : Prism.Repr}
      (hP : IsCanonical P) (hQ : IsCanonical Q) (hOrd : P ≤ Q)
      : IsCanonical (prod (cone P) (cone Q))
  -- Order and associativity
  | ord_prod {P Q S : Prism.Repr}
      (hP : IsCanonical P)
      (hCan : IsCanonical (prod (cone Q) S))
      (hOrd : P ≤ Q)
      : IsCanonical (prod (cone P) (prod (cone Q) S))


  instance isCanonical (P : Prism.Repr) : Decidable (IsCanonical P) :=
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

  -- TODO: Clean this up, it is a bit of a mess
  def toString : Prism.Repr → String
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

  instance : ToString Prism.Repr := ⟨λ P => P.toString⟩

  -- TODO: Prove termination
  -- This should be a bubble sort, for termination have a look at:
  -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Termination.20of.20bubble.20sort
  partial def toCanonical : Prism.Repr → Prism.Repr
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
    | prod _ _ => panic! "Invalid canonical form! This is a bug in Prism.Repr.toCanonical!"
  | prod P Q => 
    match P.toCanonical with
    | point => Q.toCanonical
    | cone P => (prod (cone P) Q).toCanonical
    | prod (cone P₁) P₂ => (prod (cone P₁) (prod P₂ Q)).toCanonical
    | prod _ _ => panic! "Invalid canonical form! This is a bug in Prism.Repr.toCanonical!"


  /-- toCanonical truly producees prism in canonical form -/
  @[simp]
  theorem toCanonical_IsCanonical {P : Prism.Repr} : P.toCanonical.IsCanonical := sorry_proof
  -- test_by
  --   examples:
  --     P := [segment, triangle, prism, pyramid] 
  --   counter_examples:
  --     P := [prod triangle segment, prod (cone square) (cone triangle)]

  /-
  #eval cube.toCanonical
  #eval tet.toCanonical
  #eval prism.toCanonical
  #eval pyramid.toCanonical

  #eval prod triangle segment 
  #eval prod triangle segment |>.toCanonical 

  #eval prod square segment 
  #eval prod square segment |>.toCanonical 
  
  #eval prod (cone square) (cone triangle) 
  #eval prod (cone square) (cone triangle) |>.toCanonical 
  -/

  /-- Number of `n`-dimensional faces of prism `P` -/
  def faceCount (P : Prism.Repr) (n : Nat) : Nat :=
    match P with
    | point => if n == 0 then 1 else 0
    | cone P => 
      match n with
      | 0   => 1 + P.faceCount 0
      | n+1 => P.faceCount n + P.faceCount (n+1)
    | prod P Q => ∑ i : Fin (n+1), (P.faceCount i.1) * (Q.faceCount (n-i.1))

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
  inductive Face : Prism.Repr → Type where
    | point : Face point
    | tip (P : Prism.Repr) : Face (cone P)
    | cone {P : Prism.Repr} (f : Face P) : Face (cone P)
    | base {P : Prism.Repr} (f : Face P) : Face (cone P)
    | prod {P Q : Prism.Repr} (f : Face P) (g : Face Q) 
      : Face (prod P Q)
  deriving DecidableEq

  namespace Face

  instance : Inhabited (Face P) := 
  ⟨let rec inh (P : Prism.Repr) : Face P :=
     match P with
     | .point => .point
     | .cone P => .tip P
     | .prod P Q => .prod (inh P) (inh Q)
   inh P⟩

  def toString : Face P → String 
    | point => "•"
    | tip P => s!"(tip ({P})"
    | cone f => s!"(cone {f.toString})"
    | base f => s!"(base {f.toString})"
    | prod f g => s!"({f.toString} × {g.toString})"


  instance : ToString (Face P) := ⟨Face.toString⟩

  /-- Isomorphism between faces of `P` and `P.toCanonical`. x-/
  partial def toCanonical {P} (f : Face P) : Face P.toCanonical := 
  match P, f with 
  | .point, .point => 
    have h : .point = Repr.point.toCanonical := sorry_proof
    (h ▸ .point)

  | .cone _, .tip P => 
    have h : (P.cone).toCanonical = P.toCanonical.cone := sorry_proof
    (h ▸ .tip P.toCanonical)
  | .cone P, .cone f => 
    have h : (P.cone).toCanonical = P.toCanonical.cone := sorry_proof
    (h ▸ .cone f.toCanonical)
  | .cone P, .base f => 
    have h : (P.cone).toCanonical = P.toCanonical.cone := sorry_proof
    (h ▸ .base f.toCanonical)

  | .prod P Q, .prod f g => 
    match P.toCanonical, f.toCanonical with
    | .point, _ => 
      have h : (Repr.prod P Q).toCanonical = Q.toCanonical := sorry_proof
      (h ▸ g.toCanonical)

    | .cone P', f' =>
      match Q.toCanonical, g.toCanonical with
      | .point, _ =>
        have h : (Repr.prod P Q).toCanonical = P'.cone := sorry_proof
        (h ▸ f')
      | .cone Q', g' => 
        if P' ≤ Q' then
          have h : (Repr.prod P Q).toCanonical = (.prod P'.cone Q'.cone) := sorry_proof
          (h ▸ .prod f' g')
        else
          have h : (Repr.prod P Q).toCanonical = (.prod Q'.cone P'.cone) := sorry_proof
          (h ▸ .prod g' f')

      | .prod (.cone Q₁') Q₂', .prod g₁' g₂' =>
        if P' ≤ Q₁' then
          have h : (Repr.prod P Q).toCanonical = (.prod (P'.cone) (.prod (Q₁'.cone) Q₂')) := sorry_proof
          (h ▸ .prod f' (.prod g₁' g₂'))
        else
          have h : (Repr.prod P Q).toCanonical = (.prod (Q₁'.cone) (Repr.prod (P'.cone) Q₂').toCanonical) := sorry_proof
          (h ▸ .prod g₁' (Face.prod f' g₂').toCanonical)  -- This one causes problems to the proof of termination
      | _, _ => panic! "Unreachanble code, g case! There is a bug in Face.toCanonical"
  
    | .prod (.cone P₁') P₂', .prod f₁' f₂' => 
      
      match (Repr.prod P₂' Q).toCanonical, (Face.prod f₂' g).toCanonical with

      | .cone Q', g' => 
        if P₁' ≤ Q' then
          have h : (Repr.prod P Q).toCanonical = (.prod P₁'.cone Q'.cone) := sorry_proof
          (h ▸ .prod f₁' g')
        else
          have h : (Repr.prod P Q).toCanonical = (.prod Q'.cone P₁'.cone) := sorry_proof
          (h ▸ .prod g' f₁')

      | .prod (.cone Q₁') Q₂', .prod g₁' g₂' => 
        if P₁' ≤ Q₁' then
          have h : (Repr.prod P Q).toCanonical = (.prod (P₁'.cone) (.prod (Q₁'.cone) Q₂')) := sorry_proof
          (h ▸ .prod f₁' (.prod g₁' g₂'))
        else
          have h : (Repr.prod P Q).toCanonical = (.prod (Q₁'.cone) (Repr.prod (P₁'.cone) Q₂').toCanonical) := sorry_proof
          (h ▸ .prod g₁' (Face.prod f₁' g₂').toCanonical)  -- This one causes problems to the proof of termination

      | _, _ => panic! "Unreachable code, f g case! There is a bug in Face.toCanonical"

    | _, _ => panic! "Unreachable code, f case! There is a bug in Face.toCanonical"


  /-- Isomorphism between faces of `P` and `P.toCanonical`. -/
  partial def fromCanonical {P} (f : Face P.toCanonical) : Face P := 
  match P, P.toCanonical, f with
  | .point, .point, _ => .point
  | .point, _, _ => panic! "Unreachable code in Face.fromCanonical! This is a bug! Case: .point"

  | .cone _, .cone _, .tip _ => .tip _
  | .cone P, .cone F, .cone f' => 
    have h : F = P.toCanonical  := sorry_proof
    .cone (h ▸ f').fromCanonical
  | .cone P, .cone F, .base f' => 
    have h : F = P.toCanonical  := sorry_proof
    .base (h ▸ f').fromCanonical
  | .cone _, _, _ => panic! "Unreachable code in Face.fromCanonical! This is a bug! Case: .cone P"

  | .prod .point P, F, f' => 
    have h : F = P.toCanonical := sorry_proof
    Face.prod .point (h ▸ f').fromCanonical

  | .prod (.cone P) Q, F, f' => 
    match Q.toCanonical with
    | .point => 
      have hF : F = P.cone.toCanonical := sorry_proof
      have hG : .point = Q.toCanonical := sorry_proof
      .prod (hF ▸ f').fromCanonical (hG ▸ Face.point).fromCanonical

    | .cone Q' => 
      match F, f' with
      | .prod F G, .prod f' g' =>
        let P' := P.toCanonical 
        if P' ≤ Q' then 
          have hF : F = P.cone.toCanonical := sorry_proof
          assert!   F = P.cone.toCanonical
          have hG : G = Q.toCanonical := sorry_proof
          assert!   G = Q.toCanonical
          .prod (hF ▸ f').fromCanonical (hG ▸ g').fromCanonical
        else 
          have hF : F = Q.toCanonical := sorry_proof
          assert!   F = Q.toCanonical
          have hG : G = P.cone.toCanonical := sorry_proof
          assert!   G = P.cone.toCanonical
          .prod (hG ▸ g').fromCanonical (hF ▸ f').fromCanonical
      | _, _ => panic! "Unreachable code in Face.fromCanonical! This is a bug! Case: .prod (.cone P) (.cone Q)"

    | .prod (.cone Q₁') Q₂' => 
      match F, f' with
      | .prod F G, .prod f' g' =>
        let P' := P.toCanonical 
        if P' ≤ Q₁' then
          have hF : F = P.cone.toCanonical := sorry_proof
          assert!   F = P.cone.toCanonical
          have hG : G = Q.toCanonical := sorry_proof
          assert!   G = Q.toCanonical 
          .prod (hF ▸ f').fromCanonical (hG ▸ g').fromCanonical
        else 
          -- dbg_trace s!"P: {P}\nP': {P'}\nQ: {Q}\nQ₁': {Q₁'}\nQ₂': {Q₂'}\nF: {F}\nG: {G}\nL: {Repr.prod Q₁'.cone (.prod P.cone Q₂')}\nR: {(Repr.prod P.cone Q).toCanonical}"
          have hG : G = (Repr.prod P.cone Q₂').toCanonical := sorry_proof
          assert!   G = (Repr.prod P.cone Q₂').toCanonical
          have hF : F = Q₁'.cone.toCanonical := sorry_proof
          assert!   F = Q₁'.cone.toCanonical
          let f'' := (hF ▸ f').fromCanonical
          let g'' := (hG ▸ g').fromCanonical
          match g'' with
          | .prod g₁''' g₂''' =>  
            have hQ : Repr.prod Q₁'.cone Q₂' = Q.toCanonical := sorry_proof
            assert!   Repr.prod Q₁'.cone Q₂' = Q.toCanonical 
            .prod g₁''' (hQ ▸ Face.prod f'' g₂''').fromCanonical
      | _, _ => panic! "Unreachable code in Face.fromCanonical! This is a bug! Case: .prod (.cone P) (.prod (.cone Q₁) Q₂)"
    | _ => panic! "Unreachable code in Face.fromCanonical! This is a bug! Case: .prod (.cone P) Q! There is a bug "

  | .prod P Q, FG, fg' => 
    match P.toCanonical with
    | .point => 
      have hF : .point = P.toCanonical := sorry_proof
      assert!   .point = P.toCanonical
      have hG : FG = Q.toCanonical := sorry_proof
      assert!   FG = Q.toCanonical
      .prod (hF ▸ Face.point).fromCanonical (hG ▸ fg').fromCanonical
    | .cone P' => 
      have hFG : FG = (Repr.prod P'.cone Q).toCanonical := sorry_proof
      assert!    FG = (Repr.prod P'.cone Q).toCanonical
      match (hFG ▸ fg').fromCanonical with
      | .prod f' g' => 
        have hF : P'.cone = P.toCanonical := sorry_proof
        assert!   P'.cone = P.toCanonical
        .prod (hF ▸ f').fromCanonical g'
    | .prod (.cone P₁') P₂' => 
        have hFG : FG = (Repr.prod P₁'.cone (.prod P₂' Q)).toCanonical := sorry_proof
        assert!    FG = (Repr.prod P₁'.cone (.prod P₂' Q)).toCanonical
        match (hFG ▸ fg').fromCanonical with
        | .prod f₁' (.prod f₂' g') => 
          have hF : .prod P₁'.cone P₂' = P.toCanonical := sorry_proof
          assert!   .prod P₁'.cone P₂' = P.toCanonical
          .prod (hF ▸ Face.prod f₁' f₂').fromCanonical g'
    | _ => panic! "Unreachable code in Face.fromCanonical! This is a bug! Case: .prod P Q"


  #check Nat

  -- | .cone P, _, .cone f => 
  --   have h : (P.cone).toCanonical = P.toCanonical.cone := sorry_proof
  --   sorry_proof -- .cone f.fromCanonical
  -- | .cone P, _, .base f => 
  --   have h : (P.cone).toCanonical = P.toCanonical.cone := sorry_proof
  --   sorry_proof --(h ▸ .base f.toCanonical)

  -- | .prod P Q, _, .prod f g => sorry_proof


  -- def fromCanonical {P} (f : Face P.toCanonical) : Face P := 
  -- match P, f with 
  -- | .point, .point => 
  --   have h : .point = Repr.point.toCanonical:= sorry_proof
  --   (h ▸ .point)
  -- | .cone P, _ => sorry_proof
  -- | .prod P Q, _ => sorry_proof


/--
A face of a prism is again a prism. This function converts 

---

Categorical perspective
-----------------------

A face is a inclusion of a prism `F` into a prism `P`. For a face `f : Face P`, we can obtain `F` by `f.toPrism`.

Then we can thin about `f` as a morphism `F → P` in the `Prism` category.
-/
    def toPrism {P} (f : Face P) : Prism.Repr :=
      match f with
      | point => Prism.Repr.point
      | tip P  => Prism.Repr.point
      | cone f => Prism.Repr.cone f.toPrism
      | base f => f.toPrism
      | prod f g => .prod f.toPrism g.toPrism

    /-- Dimension of a prism -/
    def dim {P} (f : Face P) : Nat := f.toPrism.dim

    /-- Face of a face is a face. For further details see `Face.ofFace` -/
    def ofFace' {P Q : Prism.Repr}
      (f : Face P) (g : Face Q) (h : f.toPrism = Q) 
      : Face P
      :=
        match f, g, h with 
        |   point,   point, _ => point
        |  tip P',   point, _ => tip P'
        | cone _,   tip _, _ => tip _
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
      := sorry_proof

    /-- The first `n`-face of `P` -/
    def first (P : Prism.Repr) (n : Nat) : Option (Face P) :=
      match P, n with
      | .point, 0 => some point
      | .point, _ => none
      | .cone P', 0 => some (tip P')
      | .cone P', n'+1 => 
        match first P' n' with
        | some f => some $ (cone f)
        | none => none
      | .prod P' Q', n =>
        Id.run do
        for i in [0:n+1] do
          match first P' i, first Q' (n-i) with
          | some f', some g' =>
            return some $ (prod f' g')
          | _, _ => continue
        none

    /-- The dimension of the first `n`-face is really `n` -/
    theorem first.dim (P: Prism.Repr) (n : Nat) (_ : n ≤ P.dim)
      : (Face.first P n).map (·.dim)  = some n := sorry_proof

    /-- The next face of the same dimension -/
    def next {P} (f : Face P) : Option (Face P) := 
      match P, f.dim, f with
      | .point, 0, point => none
      | .cone P', 0, tip _ => 
        match first P' 0 with
        | some f' => some $ base f'
        | none => none
      | .cone P', n'+1, cone f' => 
        match next f' with
        | some f'' => some $ cone f''
        | none => 
          match first P' (n'+1) with
          | some f'' => some $ base f''
          | none => none
      | .cone _, _, base f' => 
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
      | _, _, point => ⟨0, sorry_proof⟩
      | _, _, tip _ => ⟨0, sorry_proof⟩
      | _, _, cone f' => ⟨f'.toFin.1, sorry_proof⟩
      | .cone _, 0, base f' => ⟨1+f'.toFin.1, sorry_proof⟩
      | .cone P', n'+1, base f' => ⟨(P'.faceCount n')+f'.toFin.1, sorry_proof⟩
      | _, _, @prod P' Q' f' g' => 
        ⟨(∑ i : Fin f'.dim, (P'.faceCount i)*(Q'.faceCount (f.dim-i)))
         + f'.toFin.1 + g'.toFin.1 * (P'.faceCount f'.dim), sorry_proof⟩

  end Face

  def forFacesM {m} [Monad m] (P : Prism.Repr) (f : Prism.Repr.Face P → m Unit) : m Unit := do
    for d in [0:P.dim+1] do
      let mut face := Face.first P d |>.getD default
      for _ in [0:P.faceCount d] do
        f face
        face := face.next.getD default

  def forNFacesM {m} [Monad m] (P : Prism.Repr) (dim : Nat) (f : Prism.Repr.Face P → m Unit) : m Unit := do
    let mut face := Face.first P dim |>.getD default
    for _ in [0:P.faceCount dim] do
      f face
      face := face.next.getD default


  /-- Face of fixed dimension -/
  def NFace (P : Prism.Repr) (n : Nat) := {f : Face P // f.dim = n}

  namespace NFace

    instance {P} : DecidableEq (NFace P n) := by simp[NFace] infer_instance done

    def first {P n} : Option (NFace P n) :=
      match Face.first P n with
      | some f' => some ⟨f', sorry_proof⟩
      | none => none

    def next {P n} (f : NFace P n) : Option (NFace P n) :=
      match f.1.next with
      | some f' => some ⟨f', sorry_proof⟩
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
    --       base (fromFin P' 0 ⟨i.1-1, sorry_proof⟩)
    --   | Prism.cone P', n'+1, _ => 
    --     let offset := P'.faceCount n'
    --     if i.1 < offset then 
    --       cone (fromFin P' n' ⟨i.1, sorry_proof⟩)
    --     else 
    --       base (fromFin P' (n'+1) ⟨i.1 - offset, sorry_proof⟩)
    --   | Prism.prod P' Q', n, _=> Id.run do
    --     let mut offset := 0
    --     for j in [0:n+1] do
    --       let pfc := (P'.faceCount j)
    --       let qfc := (Q'.faceCount (n-j))
    --       let jcount := pfc * qfc
    --       if i.1 < offset + jcount then
    --         let i' := (i.1 - offset) % pfc
    --         let j' := (i.1 - offset) / pfc
    --         let r  := (prod (fromFin P' j ⟨i', sorry_proof⟩) 
    --                         (fromFin Q' (n-j) ⟨j', sorry_proof⟩))
    --         return ((sorry_proof : j+(n-j)=n) ▸ r)
    --       else
    --         offset := offset + jcount
    --         continue
    --     sorry_proof
    --     -- panic! "This should be unreachable!"

  end NFace

  -- def segment  := cone point
  -- def triangle := cone segment
  -- def square   := prod segment segment
  -- def tet      := cone triangle
  -- def cube     := prod segment square
  -- def pyramid  := cone square
  -- def prism    := prod segment triangle

  def analyzePrism (P : Prism.Repr) : IO Unit := do
    IO.println s!"Analyzing {P}"

    for d in [0:P.dim+1] do
      IO.println s!"  Looking at {d}-faces"

      let mut f := Face.first P d |>.getD default
      for i in [0:P.faceCount d] do

        IO.println s!"    face {i}: id:{f.toFin} | {f.toPrism} | {f.toPrism.toCanonical} | canonical: {f == f}"

        f.toPrism.forFacesM 
          λ g => IO.println s!"     {g.toPrism == (Face.ofFace g |>.toPrism)}"-- g.toPrism.forFacesM 

        f.toCanonical.toPrism.forFacesM 
          λ g => IO.println s!"     {g.toCanonical.fromCanonical == g}"-- g.toPrism.forFacesM 

        --     λ h => 
        --       let h'  := Face.ofFace h
        --       let h'' := Face.ofFace h'
        --       IO.println s!"{h''}"
        -- -- IO.println ""
        f := f.next.getD default


  #eval analyzePrism triangle
  #eval analyzePrism (point.prod (square.prod point))

  #eval analyzePrism pyramid

  #eval analyzePrism (triangle.prod segment)

  -- ((tip (•) × ((cone •) × (tip (• ∧ •)))

  -- #eval analyzePrism ((cube).cone.prod triangle)

  #eval ((cube).cone.prod triangle).dim

  -- #eval point.prod segment 



#exit

  #eval (
    (do
      let mut it := Face.first prism 2
      for i in [0:100] do
        match it with
        | some f => do
          IO.print s!"{f.toFin}: "
          -- IO.print s!"{f.toPrism}: "
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

  def pos {P : Prism} : NFace P 0 → P.𝔼 := sorry_proof
  -- def pos {P : Prism} : Fin (P.pointCount) → ℝ^P.dim := sorry_proof

  -- def toRn : {P : Prism} → P.E → ℝ^P.dim := sorry_proof
  -- def fromRn : {P : Prism} → ℝ^P.dim → P.E := sorry_proof

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

  -- def barycentricCoord {P : Prism} : Fin (P.pointCount) → ℝ^P.dim → ℝ := sorry_proof

  -- embedding map from a face to prism
  def Face.embed {P} (f : Face P) : f.toPrism.𝔼 → P.𝔼 := sorry_proof


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

