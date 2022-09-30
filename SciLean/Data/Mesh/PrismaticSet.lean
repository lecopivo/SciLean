import SciLean.Data.Mesh.Prism

namespace SciLean


  namespace Prism
  -- open Prism



  structure PrismaticSet where 
    /-- Index set for Elems of type `P` -/
    Elem (P : Prism) : Type     
    -- Index set for cofaces of `e` of type `Q`
    CofaceIndex {Q} (e : Elem Q) (P : Prism) : Type

    /-- Face of `e` of type `Q` given an inclusion of `Q` to `P` -/
    face {Q P} (f : Inclusion Q P) (e : Elem P) : Elem Q
    /-- Coface is a -/
    coface {Q} {e : Elem Q} {P : Prism} : CofaceIndex e P → Inclusion Q P × Elem P

    -- consitency between face and coface
    face_coface : ∀ (e : Elem Q) (P : Prism) (i : CofaceIndex e P), 
      Function.uncurry face (coface i) = e

    -- Contravariant functoriality - i.e. PrismaticSet is a presheaf
    face_comp {P Q S : Prism} : ∀ (f : Inclusion Q P) (g : Inclusion S Q),
      (face (f ∘ g)) = face g ∘ face f

  def Foo (P : Prism) : Type :=
    match P.nrepr with
    | .point => Int
    | .cone .point => Int
    | _ => Empty

  def segment' : Prism := ⟦⟨.cone .point, .any, sorry_proof, sorry_proof⟩⟧
  def segment'' : Prism := ⟦.any| PrismRepr.point.cone⟧

  example : segment' = segment := by native_decide
  example : segment' = segment := by rfl
  example : segment'' = segment := by rfl
  example : segment'' = segment' := by rfl
  example : Foo point = Int   := by rfl
  example : Foo segment = Int := by rfl
  example : Foo segment' = Int := by rfl
  example : Foo cube = Empty  := by rfl

  #check Nonempty 

  open Lean.Parser.Tactic in
  macro "cast_elem" "[" h:simpLemma,* "]" x:term : term => `(cast (by simp[$h:simpLemma,*,PrismRepr.toCanonical,FaceRepr.toPrism, FaceRepr.ofPrism] done) $x)

  def Line : PrismaticSet :=
  {
    Elem := λ P => 
      match P.nrepr with 
      | .point => Int
      | .cone .point => Int
      | _ => Empty

    face := λ {Q P} f e =>
      let f' := f.1.nrepr
      have hQ : Q.nrepr = f'.toPrism.toCanonical := sorry
      have hP : P.nrepr = f'.ofPrism := sorry
      -- have hQ : Q = f.1.toPrism := sorry
      -- have hP : P = f.1.ofPrism := sorry
      match f', e, hQ, hP with
      -- identity on point
      | .point, e, h1, h2 => cast_elem [h1,h2] e
      -- identity on segment
      | .cone .point, e, h1, h2 => cast_elem [h1,h2] e

      -- start point of a segment
      | .base .point, e, h1, h2 => cast_elem [h1,h2] e
      -- end point of a segment
      | .tip .point, e, h1, h2 =>
        let e : Int := cast_elem [h2] e
        cast_elem [h1] (e+1)
      | _, e, h1, h2 => absurd (a := Nonempty Empty) sorry_proof sorry_proof /- `e` is element of Empty -> contradiction, how to prove this? -/

    CofaceIndex := 
      λ {Q} _ P => 
      match Q.nrepr, P.nrepr with
      -- neighbours of a point
      | .point, .point => Unit
      | .point, .cone .point => Fin 2
      | .point, _ => Empty

      -- neighbours of a segment
      | .cone .point, .cone .point => Unit
      | .cone .point, _ => Empty

      -- all the rest is empty
      | _, _ => Empty

    coface := 
      λ {Q} e P id =>  -- Q.nrepr = f'.toPrism.toCanonical
      have hQ : Q = ⟦.any| Q.nrepr⟧ := sorry_proof
      have hP : P = ⟦.any| P.nrepr⟧ := sorry_proof
      match Q.nrepr, P.nrepr, hQ, hP with
      -- neighbours of a point
      | .point, .point, hQ, hP => 
        let e : Int := cast sorry_proof e
        (⟨⟦.any| .point⟧, sorry_proof, sorry_proof⟩, cast sorry_proof e)
      | .point, .cone .point, hQ, hP => 
        let id : Fin 2 := cast sorry_proof id
        let e  : Int   := cast sorry_proof e
        if id = 0 
        then (⟨⟦.any| .tip .point⟧, sorry_proof, sorry_proof⟩, cast sorry_proof (e-1))
        else (⟨⟦.any| .base .point⟧, sorry_proof, sorry_proof⟩, cast sorry_proof e)

      -- neighbours of a segment is the segment itself
      | .cone .point, .cone .point, hQ, hP => 
        let e : Int := cast sorry_proof e
        (⟨⟦.any| .cone .point⟧, sorry_proof, sorry_proof⟩, cast sorry_proof e)
      | _, _, e, _ => absurd (a := Nonempty Empty) sorry_proof sorry_proof /- `e` is element of Empty -> contradiction, how to prove this? -/

    face_coface := λ e p i => sorry_proof
    face_comp := λ f g => sorry_proof
  }

  -- Test defeq of elements
  example : Line.Elem point    = ℤ := by rfl
  def point1 : Line.Elem point := (0 : ℤ)   -- good!
  -- def edge1 : Line.Elem segment' := (0 : ℤ) -- why does this fail?
  example : Line.Elem segment' = ℤ := by rfl
  example : Line.Elem segment  = ℤ := by rfl

  #check Nat

  def segmentStart : (Face segment 0) := Face.mk ⟦.any| .base .point⟧ sorry_proof sorry_proof
  def segmentEnd   : (Face segment 0) := Face.mk ⟦.any|  .tip .point⟧ sorry_proof sorry_proof

  def segmentSrc : Inclusion point segment' := Inclusion.mk ⟦.any| .base .point⟧ sorry_proof sorry_proof
  def segmentTrg : Inclusion point segment' := Inclusion.mk ⟦.any|  .tip .point⟧ sorry_proof sorry_proof

  example : Line.Elem segment' = ℤ := by rfl
  def zero : ℤ := 0
  def zero' : Line.Elem segment' := cast (by rfl) (0 : ℤ)
  
  #check Line.face segmentSrc zero
  #check reduce_type_of (Line.face segmentTrg zero')
    
  def Circle (n : Nat) : PrismaticSet :=
  {
    Elem := λ P => 
      match P.nrepr with 
      | .point => Fin n
      | .cone .point => Fin n
      | _ => Empty

    face := λ {Q P} f e =>
      let f' := f.1.nrepr
      have hQ : Q.nrepr = f'.toPrism.toCanonical := sorry
      have hP : P.nrepr = f'.ofPrism := sorry
      -- have hQ : Q = f.1.toPrism := sorry
      -- have hP : P = f.1.ofPrism := sorry
      match f', e, hQ, hP with
      -- identity on point
      | .point, e, h1, h2 => cast_elem [h1,h2] e
      -- identity on segment
      | .cone .point, e, h1, h2 => cast_elem [h1,h2] e

      -- start point of a segment
      | .base .point, e, h1, h2 => cast_elem [h1,h2] e
      -- end point of a segment
      | .tip .point, e, h1, h2 =>
        let e : Fin n := cast_elem [h2] e
        cast_elem [h1] (e+⟨1,sorry_proof⟩)
      | _, e, h1, h2 => absurd (a := Nonempty Empty) sorry_proof sorry_proof /- `e` is element of Empty -> contradiction, how to prove this? -/

    CofaceIndex := 
      λ {Q} _ P => 
      match Q.nrepr, P.nrepr with
      -- neighbours of a point
      | .point, .point => Unit
      | .point, .cone .point => Fin 2
      | .point, _ => Empty

      -- neighbours of a segment
      | .cone .point, .cone .point => Unit
      | .cone .point, _ => Empty

      -- all the rest is empty
      | _, _ => Empty

    coface := 
      λ {Q} e P id =>  -- Q.nrepr = f'.toPrism.toCanonical
      have hQ : Q = ⟦.any| Q.nrepr⟧ := sorry_proof
      have hP : P = ⟦.any| P.nrepr⟧ := sorry_proof
      match Q.nrepr, P.nrepr, hQ, hP with
      -- neighbours of a point
      | .point, .point, hQ, hP => 
        let e : Fin n := cast sorry_proof e
        (⟨⟦.any| .point⟧, sorry_proof, sorry_proof⟩, cast sorry_proof e)
      | .point, .cone .point, hQ, hP => 
        let id : Fin 2 := cast sorry_proof id
        let e  : Fin n := cast sorry_proof e
        if id = 0 
        then (⟨⟦.any| .tip .point⟧, sorry_proof, sorry_proof⟩, cast sorry_proof (e-⟨1,sorry_proof⟩))
        else (⟨⟦.any| .base .point⟧, sorry_proof, sorry_proof⟩, cast sorry_proof e)

      -- neighbours of a segment is the segment itself
      | .cone .point, .cone .point, hQ, hP => 
        let e : Fin n := cast sorry_proof e
        (⟨⟦.any| .cone .point⟧, sorry_proof, sorry_proof⟩, cast sorry_proof e)
      | _, _, e, _ => absurd (a := Nonempty Empty) sorry_proof sorry_proof /- `e` is element of Empty -> contradiction, how to prove this? -/

    face_coface := λ e p i => sorry_proof
    face_comp := λ f g => sorry_proof
  }

  @[simp high]
  theorem nrepr_of_quotient (P : PrismRepr) (l) : Prism.nrepr ⟦l| P ⟧ = P.toCanonical := sorry_proof
  @[simp]
  theorem toCanonical_of_point : PrismRepr.point.toCanonical = .point := by simp[PrismRepr.toCanonical]; done
  @[simp]
  theorem toCanonical_of_segment : PrismRepr.point.cone.toCanonical = .cone .point := by simp[PrismRepr.toCanonical]; done



  instance (n : Nat) (P : Prism) : Enumtype ((Circle n).Elem P) := 
    have hP : P = ⟦.any| P.nrepr⟧ := sorry_proof
    match P.nrepr, hP with
    | .point, hP => by simp[PrismaticSet.Elem, Circle]; simp only [hP, nrepr_of_quotient]; simp; infer_instance
    | .cone .point, hP =>  by simp[PrismaticSet.Elem, Circle]; simp only [hP, nrepr_of_quotient]; simp; infer_instance
    | _, hP => 
      let enum : Enumtype Empty := by infer_instance
      cast sorry enum

   instance (n Q P) (e : (Circle n).Elem Q) : Enumtype ((Circle n).CofaceIndex e P) :=
     have hQ : Q = ⟦.any| P.nrepr⟧ := sorry_proof
     have hP : P = ⟦.any| P.nrepr⟧ := sorry_proof
     match Q.nrepr, P.nrepr, hQ, hP with
     -- neighbours of a point
     | .point, .point, hQ, hP =>  by simp[PrismaticSet.Elem, Circle]; simp only [hP, hQ, nrepr_of_quotient]; simp; infer_instance
     | .point, .cone .point, hQ, hP => by simp[PrismaticSet.Elem, Circle]; simp only [hP, hQ, nrepr_of_quotient]; simp; infer_instance
     | .point, _, hQ, hP => 
       let enum : Enumtype Empty := by infer_instance
       cast sorry enum

     -- neighbours of a segment
     | .cone .point, .cone .point, hQ, hP => by simp[PrismaticSet.Elem, Circle]; simp only [hP, hQ, nrepr_of_quotient]; simp; infer_instance
     | .cone .point, _, hQ, hP => 
       let enum : Enumtype Empty := by infer_instance
       cast sorry enum

     -- all the rest is empty
     | _, _, hQ, hP => 
       let enum : Enumtype Empty := by infer_instance
       cast sorry enum

  def Segment (n : Nat) : PrismaticSet :=
  {
    Elem := λ P => 
      match P.nrepr with 
      | .point => Fin (n + 1)
      | .cone .point => Fin n
      | _ => Empty

    face := λ {Q P} f e =>
      let f' := f.1.nrepr
      have hQ : Q.nrepr = f'.toPrism.toCanonical := sorry
      have hP : P.nrepr = f'.ofPrism := sorry
      match f', e, hQ, hP with
      -- identity on point
      | .point, e, h1, h2 => cast_elem [h1,h2] e

      -- identity on segment
      | .cone .point, e, h1, h2 => cast_elem [h1,h2] e

      -- start point of a segment
      | .base .point, e, h1, h2 => 
        let e : Fin n       := cast_elem [h2] e
        let e : Fin (n + 1) := ⟨e.1, Nat.lt_succ_of_lt e.2⟩
        cast_elem [h1] e

      -- end point of a segment
      | .tip .point, e, h1, h2 => 
        let e : Fin n     := cast_elem [h2] e
        let e : Fin (n+1) := ⟨e.1 + 1, Nat.succ_lt_succ e.2⟩
        cast_elem [h1] e
      | _, e, h1, h2 => absurd (a := Nonempty Empty) sorry_proof sorry_proof /- `e` is element of Empty -> contradiction, how to prove this? -/

    CofaceIndex := 
      λ {Q} e P => 
      match Q.nrepr, P.nrepr with
      -- neighbours of a point
      | .point, .point => Unit
      | .point, .cone .point => 
        let e : Fin (n+1) := cast sorry_proof e
        if (e = 0) ∨ (e = n)
        then Unit
        else Fin 2
      | .point, _ => Empty

      -- neighbours of a segment
      | .cone .point, .cone .point => Unit
      | .cone .point, _ => Empty

      -- all the rest is empty
      | _, _ => Empty

    coface := 
      λ {Q} e P id =>  -- Q.nrepr = f'.toPrism.toCanonical
      have hQ : Q = ⟦.any| Q.nrepr⟧ := sorry_proof
      have hP : P = ⟦.any| P.nrepr⟧ := sorry_proof
      match Q.nrepr, P.nrepr, hQ, hP with
      -- neighbours of a point
      | .point, .point, hQ, hP => 
        let e : Fin n := cast sorry_proof e
        (⟨⟦.any| .point⟧, sorry_proof, sorry_proof⟩, cast sorry_proof e)
      | .point, .cone .point, hQ, hP => 
        let e  : Fin (n+1) := cast sorry_proof e
        let id : Fin 2 := 
          if      (e = 0) then 1
          else if (e = n) then 0
          else (cast sorry_proof id)
        if id = 0 
        then (⟨⟦.any| .tip .point⟧, sorry_proof, sorry_proof⟩, cast sorry_proof (e-⟨1,sorry_proof⟩))
        else (⟨⟦.any| .base .point⟧, sorry_proof, sorry_proof⟩, cast sorry_proof e)

      -- neighbours of a segment is the segment itself
      | .cone .point, .cone .point, hQ, hP => 
        let e : Fin n := cast sorry_proof e
        (⟨⟦.any| .cone .point⟧, sorry_proof, sorry_proof⟩, cast sorry_proof e)
      | _, _, _, _ => absurd (a := Nonempty Empty) sorry_proof sorry_proof /- `e` is element of Empty -> contradiction, how to prove this? -/

    face_coface := λ e p i => sorry_proof
    face_comp := λ f g => sorry_proof
  }

  -- TODO:
  --  1. product 
  --  1. sum 
  --  2. quotient -- decidable equality? that is probably the hardest thing
  --  3. caching -- stamps out face maps to index arrays 
                 -- explicit boundary maps -- potential for computing homologies
 
end SciLean.Prism

namespace SciLean

open Prism

  -- This is Enumtype
  structure PrismDecomposition (P : Prism) where
    fst : Prism
    snd : Prism
    property : P = fst * snd

  -- -- This is Enumtype if `S₁.FaceIndex P` and `S₂.FaceIndex P` are Enumtypes
  -- structure PrismaticSet'.ProdFaceIndex (P : Prism) (S₁ S₂ : PrismaticSet') where
  --   dec : PrismDecomposition P
  --   Elem₁ : S₁.Elem dec.fst
  --   Elem₂ : S₂.Elem dec.snd

  structure PrismaticSet.ProdElem (P : Prism) (Elem₁ Elem₂ : Prism → Type) where
    dec : PrismDecomposition P
    fst : Elem₁ dec.fst
    snd : Elem₂ dec.snd

  def Face.split {P : Prism l} (f : Face P n) (P₁ P₂ : Prism l) (h : P = P₁ * P₂) : Face P₁ × Face P₂ :=
    match f.1.nrepr.fromCanonical (P₁.nrepr.prod P₂.nrepr) sorry_proof with
    | .prod f₁ f₂ =>
      (⟨⟦l|f₁⟧, sorry_proof, by simp⟩, ⟨⟦l|f₂⟧, sorry_proof, by simp⟩)
    | _ => absurd (a := True) sorry_proof sorry_proof /- fromCanonical (P * Q) has to be always a face of type .prod f g -/


  def PrismaticSet.prod (S₁ S₂ : PrismaticSet) : PrismaticSet :=
  {
    Elem := λ P => ProdElem P S₁.Elem S₂.Elem
    CofaceIndex := λ e Q => ProdElem Q (S₁.CofaceIndex e.fst) (S₂.CofaceIndex e.snd)

    face := λ {Q _} ι e => 
      let P₁ := e.dec.fst
      let P₂ := e.dec.snd
      let (f₁, f₂) := ι.toFace.split P₁ P₂ e.dec.property
      let Q₁ := f₁.toPrism
      let Q₂ := f₂.toPrism
      let Qdec : PrismDecomposition Q := ⟨Q₁, Q₂, sorry_proof⟩
      let ι₁ : Inclusion Q₁ P₁ := ⟨f₁.1, sorry_proof, sorry_proof⟩
      let ι₂ : Inclusion Q₂ P₂ := ⟨f₂.1, sorry_proof, sorry_proof⟩
      ⟨Qdec, S₁.face ι₁ e.fst, S₂.face ι₂ e.snd⟩

    coface := λ {Q e P} ⟨dec, f₁', f₂'⟩ =>
      let (ι₁, e₁) := S₁.coface f₁'
      let (ι₂, e₂) := S₂.coface f₂'
      let ι : Inclusion Q P  := ⟨ι₁.1 * ι₂.1, sorry_proof, sorry_proof⟩
      let e : ProdElem P _ _ := ⟨dec, e₁, e₂⟩
      (ι, e)

    face_coface := sorry_proof
    face_comp := sorry_proof
  }
