import SciLean.Data.Mesh.Prism

namespace SciLean


  open Prism

/-- Generalization of semi-simplicial set(also callsed Δ-set).

It is not generalization of simplicial set as it does not have degenerate prisms.


Categorical view
================

`PrismaticSet` is a presheaf on the catogory of `Prism`. The `Elem` function maps prisms to types. The `face` function maps prism inclusion to functions between types `Elem P`.

-/
structure PrismaticSet where
  /-- Index set for Elems of type `P` -/
  Elem (P : Prism) : Type

  /-- Face of `e` of type `Q` given an inclusion of `Q` to `P` -/
  face {Q P} (f : Inclusion Q P) (e : Elem P) : Elem Q

  -- Contravariant functoriality - i.e. PrismaticSet is a presheaf
  face_comp {P Q S : Prism} : ∀ (f : Inclusion Q P) (g : Inclusion S Q),
    (face (f.comp g)) = (face g).comp (face f)

namespace PrismaticSet

/-- Coface interface of a prismatic set.

The `coface` function is not included in `PrismaticSet` as it is not always necessary and computing all the neighbouring information can be costly.

Categorical view
================

What is the categorical point of view of `coface`? Maybe adjunction of something? I don't know. Figuring this out might improve the interface and make it more composable.
-/
class Coface (S : PrismaticSet) where
  -- Index set for cofaces of `e` of type `Q`
  CofaceIndex {Q} (e : S.Elem Q) (P : Prism) : Type

  /-- Coface is a -/
  coface {Q} {e : S.Elem Q} {P : Prism} : CofaceIndex e P → Inclusion Q P × S.Elem P

  -- consitency between face and coface
  face_coface : ∀ (e : S.Elem Q) (P : Prism) (i : CofaceIndex e P),
    Function.uncurry S.face (coface i) = e


abbrev CofaceIndex (S : PrismaticSet) [Coface S] {Q} (e : S.Elem Q) (P : Prism)
  := Coface.CofaceIndex e P

abbrev coface (S : PrismaticSet) [Coface S] {Q} {e : S.Elem Q} {P} (id : S.CofaceIndex e P)
  := Coface.coface id

abbrev pointCount (S : PrismaticSet) [Enumtype (S.Elem point)] := numOf (S.Elem point)
abbrev edgeCount (S : PrismaticSet) [Enumtype (S.Elem segment)] := numOf (S.Elem segment)
abbrev triangleCount (S : PrismaticSet) [Enumtype (S.Elem triangle)] := numOf (S.Elem triangle)

-- TODO:
--  1. product
--  1. sum
--  2. quotient -- decidable equality? that is probably the hardest thing
--  3. caching -- stamps out face maps to index arrays
               -- explicit boundary maps -- potential for computing homologies

structure ProdElem (P : Prism) (Elem₁ Elem₂ : Prism → Type) where
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
  numOf := Enumtype.sum λ dec : PrismDecomposition P => numOf (Elem₁ dec.fst) * numOf (Elem₂ dec.snd)

  toFin := λ e => Id.run do
    let mut N := 0
    for dec in Iterable.fullRange (PrismDecomposition P) do
      if dec = e.dec then
        break
      else
        N += numOf (Elem₁ dec.fst) * numOf (Elem₂ dec.snd)
    -- let N := ∑ dec < e.dec, numOf (Elem₁ dec.fst) * numOf (Elem₂ dec.snd)
    ⟨(toFin e.fst).1 * numOf (Elem₂ e.dec.snd) + (toFin e.snd).1 + N, sorry_proof⟩

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


def prod (S₁ S₂ : PrismaticSet) : PrismaticSet :=
{
  Elem := λ P => ProdElem P S₁.Elem S₂.Elem

  face := λ ι e =>
    let ιDec := ι.split e.dec
    let (ι₁,ι₂) := ιDec.2
    -- dbg_trace s!"{ι₁.repr} | {ι₂.repr}"
    ⟨ιDec.1, S₁.face ι₁ e.fst, S₂.face ι₂ e.snd⟩
    -- ⟨ιDec.1, cast sorry 0, cast sorry 0⟩

  face_comp := sorry_proof
}

instance (S₁ S₂ : PrismaticSet) [Coface S₁] [Coface S₂] : Coface (S₁.prod S₂) where

  CofaceIndex := λ e P => ProdElem P (S₁.CofaceIndex e.fst) (S₂.CofaceIndex e.snd)

  coface := λ {Q _ P} ⟨dec, f₁', f₂'⟩ =>
    let (ι₁, e₁) := S₁.coface f₁'
    let (ι₂, e₂) := S₂.coface f₂'
    let ι : Inclusion Q P  := ⟨(ι₁.repr.prod ι₂.repr).toCanonical, sorry_proof, sorry_proof⟩
    let e : ProdElem P _ _ := ⟨dec, e₁, e₂⟩
    (ι, e)

  face_coface := sorry_proof

instance (S₁ S₂ : PrismaticSet) [∀ P, Enumtype (S₁.Elem P)] [∀ P, Enumtype (S₂.Elem P)] (P : Prism)
  : Enumtype ((PrismaticSet.prod S₁ S₂).Elem P) := by unfold PrismaticSet.prod; infer_instance

instance (S₁ S₂ : PrismaticSet) [Coface S₁] [Coface S₂]
  [∀ Q (e : S₁.Elem Q) P, Enumtype (S₁.CofaceIndex e P)]
  [∀ Q (e : S₂.Elem Q) P, Enumtype (S₂.CofaceIndex e P)]
  (Q) (e : (PrismaticSet.prod S₁ S₂).Elem Q) (P)
  : Enumtype ((PrismaticSet.prod S₁ S₂).CofaceIndex e P) := by unfold PrismaticSet.prod; unfold PrismaticSet.CofaceIndex; simp[Coface.CofaceIndex]; infer_instance
