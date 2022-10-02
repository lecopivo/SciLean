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
  -- #check reduce_type_of (Line.face segmentTrg zero')
    
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

  structure PrismaticSet.ProdElem (P : Prism) (Elem₁ Elem₂ : Prism → Type) where
    dec : PrismDecomposition P
    fst : Elem₁ dec.fst
    snd : Elem₂ dec.snd

  instance [∀ P, Iterable (Elem₁ P)] [∀ P, Iterable (Elem₂ P)] 
    : Iterable (PrismaticSet.ProdElem P Elem₁ Elem₂) :=
  {
    first := Id.run do
      for dec in Iterable.fullRange (PrismDecomposition P) do
        match Iterable.first (ι := Elem₁ dec.fst), Iterable.first (ι := Elem₂ dec.snd) with
        | some fst, some snd => return (some ⟨dec, fst, snd⟩)
        | _, _ => continue
      none

    next  := λ elem => 
      match Iterable.next elem.snd with
      | some snd' => some ⟨elem.dec, elem.fst, snd'⟩
      | none => 
        match (Iterable.next elem.fst), (Iterable.first (ι := Elem₂ elem.dec.snd)) with
        | some fst', some snd' => some ⟨elem.dec, fst', snd'⟩
        | _, _ =>
          match Iterable.next elem.dec with
          | some dec => Id.run do
            let range : Iterable.LinRange (PrismDecomposition P) := some (dec, none)
            for dec' in range do
              match Iterable.first (ι := Elem₁ dec'.fst), Iterable.first (ι := Elem₂ dec'.snd) with
              | some fst', some snd' => return (some ⟨dec', fst', snd'⟩)
              | _, _ => continue
            none
          | none => none
    
    decEq := λ elem elem' =>
      if h : elem.dec = elem'.dec 
        then if
         elem.fst = (h ▸ elem'.fst) ∧
         elem.snd = (h ▸ elem'.snd)
        then 
          isTrue sorry_proof
        else 
          isFalse sorry_proof
      else
        isFalse sorry_proof
  }

  instance [∀ P, Enumtype (Elem₁ P)] [∀ P, Enumtype (Elem₂ P)] 
    : Enumtype (PrismaticSet.ProdElem P Elem₁ Elem₂) :=
  {
    numOf := ∑ dec : PrismDecomposition P, numOf (Elem₁ dec.fst) * numOf (Elem₂ dec.snd)

    toFin := λ e => Id.run do
      let mut N := 0
      for dec in Iterable.fullRange (PrismDecomposition P) do
        if dec = e.dec then
          break
        else 
          N += numOf (Elem₁ dec.fst) * numOf (Elem₂ dec.snd)
      -- let N := ∑ dec < e.dec, numOf (Elem₁ dec.fst) * numOf (Elem₂ dec.snd)
      ⟨(toFin e.fst).1 * (toFin e.snd).1 + N, sorry_proof⟩

    fromFin := λ i => Id.run do
      let mut id : Nat := i.1
      for dec in Iterable.fullRange (PrismDecomposition P) do
        let N₁ := numOf (Elem₁ dec.fst)
        let N₂ := numOf (Elem₂ dec.fst)
        let N := N₁ * N₂
        if id < N then
          let i := id / N₂
          let j := id % N₂
          return ⟨dec, fromFin ⟨i,sorry_proof⟩, fromFin ⟨j,sorry_proof⟩⟩
        else
          id -= N
      absurd (a:= True) sorry_proof sorry_proof -- This should not happed

    first_fromFin := sorry_proof
    next_fromFin  := sorry_proof
    next_toFin    := sorry_proof
  }


  def PrismaticSet.prod (S₁ S₂ : PrismaticSet) : PrismaticSet :=
  {
    Elem := λ P => ProdElem P S₁.Elem S₂.Elem
    CofaceIndex := λ e P => ProdElem P (S₁.CofaceIndex e.fst) (S₂.CofaceIndex e.snd)

    face := λ ι e => 
      let ιDec := ι.split e.dec
      let (ι₁,ι₂) := ιDec.2
      ⟨ιDec.1, S₁.face ι₁ e.fst, S₂.face ι₂ e.snd⟩

    coface := λ {Q e P} ⟨dec, f₁', f₂'⟩ =>
      let (ι₁, e₁) := S₁.coface f₁'
      let (ι₂, e₂) := S₂.coface f₂'
      let ι : Inclusion Q P  := ⟨ι₁.1 * ι₂.1, sorry_proof, sorry_proof⟩
      let e : ProdElem P _ _ := ⟨dec, e₁, e₂⟩
      (ι, e)

    face_coface := sorry_proof
    face_comp := sorry_proof
  }


  instance (S₁ S₂ : PrismaticSet) [∀ P, Enumtype (S₁.Elem P)] [∀ P, Enumtype (S₂.Elem P)] (P : Prism)
    : Enumtype ((PrismaticSet.prod S₁ S₂).Elem P) := by unfold PrismaticSet.prod; infer_instance

  instance (S₁ S₂ : PrismaticSet) 
    [∀ Q (e : S₁.Elem Q) P, Enumtype (S₁.CofaceIndex e P)] 
    [∀ Q (e : S₂.Elem Q) P, Enumtype (S₂.CofaceIndex e P)] 
    (Q) (e : (PrismaticSet.prod S₁ S₂).Elem Q) (P)
    : Enumtype ((PrismaticSet.prod S₁ S₂).CofaceIndex e P) := by unfold PrismaticSet.prod; infer_instance
