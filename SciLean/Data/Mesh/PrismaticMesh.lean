import SciLean.Data.Mesh.PrismaticSet

namespace SciLean

  structure MeshPos (S : PrismaticSet) where
    prism : Prism
    elem : S.Elem prism
    pos : ℝ^{prism.dim}


  -- Mesh embeded in a vector space X
  -- It should extend PrismaticSet, but there is some problem with 
  structure PrismaticMesh (X : Type) [Vec X] extends PrismaticSet where
    toPos : (MeshPos toPrismaticSet) → X
    closestPoint : X → (MeshPos toPrismaticSet)

    -- Continuity across faces
    toPos_face (Q P : Prism) (ι : Inclusion Q P) (e : Elem P) (x : ℝ^{Q.dim}) (h : Q.InPrism x)
      : toPos ⟨P, e, ι.faceInclusion x⟩ = toPos ⟨Q, face ι e, x⟩
    
    -- Point on the mesh is the closes point
    closestPoint_toPos (p : MeshPos toPrismaticSet) : closestPoint (toPos p) = p

  
  def PrismaticMesh.prod {X Y} [Vec X] [Vec Y] (M : PrismaticMesh X) (N : PrismaticMesh Y) : PrismaticMesh (X×Y) :=
    PrismaticMesh.mk (M.toPrismaticSet.prod N.toPrismaticSet)
      (toPos := λ p => 
        let dim₁ := p.elem.dec.fst.dim
        let dim₂ := p.elem.dec.snd.dim
        let x₁ : ℝ^{dim₁} := λ [i] => p.pos[⟨i.1, sorry_proof⟩]
        let x₂ : ℝ^{dim₂} := λ [i] => p.pos[⟨i.1 + dim₁, sorry_proof⟩]
        let p₁ : MeshPos M.toPrismaticSet := ⟨p.elem.dec.fst, p.elem.fst, x₁⟩
        let p₂ : MeshPos N.toPrismaticSet := ⟨p.elem.dec.snd, p.elem.snd, x₂⟩
        let pos₁ := M.toPos p₁
        let pos₂ := N.toPos p₂
        (pos₁, pos₂))

      (closestPoint := λ (x,y) => 
        let p₁ := M.closestPoint x        
        let p₂ := N.closestPoint y
        let P := p₁.prism * p₂.prism
        let decP := P.decomposeBy p₁.prism
        ⟨P, 
        ⟨decP, cast sorry_proof p₁.elem, cast sorry_proof p₂.elem⟩, 
        λ [i] => if i.1 < p₁.prism.dim 
                 then p₁.pos[⟨i.1, sorry_proof⟩]
                 else p₂.pos[⟨i.1 - p₁.prism.dim, sorry_proof⟩]⟩)

      (toPos_face := sorry_proof)
      (closestPoint_toPos := sorry_proof)
