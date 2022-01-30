import SciLean.Data.Mesh.Prism

namespace SciLean.Prism

  open Prism

  structure PrismaticSet where 
    X : Prism → Type
    face {P} : (f : Face P) → X P → X f.toPrism
    -- Contravariant functoriality - i.e. PrismaticSet is a presheaf
    face_of_face {P} : ∀ (f : Face P) (g : Face f.toPrism),
      let h : Face.toPrism (Face.ofFace g) = Face.toPrism g := by simp
      face (Face.ofFace g) = (h ▸ face g ∘ face f)

  def Line : PrismaticSet :=
  {
    X := λ P =>
      match P with 
      | point => Int
      | cone point => Int
      | _ => Empty
    face := λ {P} f p => 
      match P, f, p with
      | point, Face.point, p => p
      | cone point, Face.cone (Face.point), p => p
      | cone point, Face.tip _, p => p
      | cone point, Face.base Face.point, p => 
        by simp[Face.toPrism]; simp at p;
           apply (p+1)
           done
    face_of_face := sorry
  }
    
  def Circle (n : Nat) : PrismaticSet :=
  {
    X := λ P =>
      match P with
      | point => Fin n
      | cone point => Fin n
      | _ => Empty
    face := λ {P} f p => 
      match P, f, p with
      | point, Face.point, p => p
      | cone point, Face.cone (Face.point), p => p
      | cone point, Face.tip _, p => p
      | cone point, Face.base Face.point, p => 
        by simp[Face.toPrism]; simp at p;
           apply (match n, p with
                  | n+1, p => p + 1)
           done
    face_of_face := sorry
  }

  def Segment (n : Nat) : PrismaticSet :=
  {
    X := λ P => 
      match P with
      | point => Fin (n+1)
      | cone point => Fin n
      | _ => Empty
    face := λ {P} f p => 
      match P, f, p with
      | point, Face.point, p => p
      | cone point, Face.cone (Face.point), p => p
      | cone point, Face.tip _, p => !p.1
      | cone point, Face.base Face.point, p => 
        by simp[Face.toPrism]; simp at p;
           apply (match n, p with
                  | n+1, p => (p.1 + 1))
           done
    face_of_face := sorry
  }

  -- TODO:
  --  1. product 
  --  1. sum 
  --  2. quotient -- decidable equality? that is probably the hardest thing
  --  3. caching -- stamps out face maps to index arrays 
                 -- explicit boundary maps -- potential for computing homologies

  variable (PP : Prism)
  #check {P : (Prism × Prism) // prod P.1 P.2 = PP}

  def PrismaticSet.Prod (S R : PrismaticSet) : PrismaticSet :=
  {
    X := λ P : Prism => 
      -- TODO: Add condition that pq.1 and pq.2 are in normalized form
      PSigma (λ P' : {pq : Prism × Prism // prod pq.1 pq.2 = P} => S.X P'.1.1 × R.X P'.1.2)
    face := sorry
    face_of_face := sorry
  }
