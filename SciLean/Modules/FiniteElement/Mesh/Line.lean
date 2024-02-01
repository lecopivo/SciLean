import SciLean.Data.Mesh.PrismaticMesh

namespace SciLean

  open Prism

  def LineSet : PrismaticSet :=
  {
    Elem := λ P =>
      match P with
      | ⟨.point, _⟩ => Int
      | ⟨.cone .point, _⟩ => Int
      | _ => Empty

    face := λ {Q P} f e =>
      match Q, P, f, e with
      -- identity on point
      | ⟨.point, _⟩, ⟨.point, _⟩, ⟨.point, _, _⟩, e => e
      -- identity on segment
      | ⟨.cone .point, _⟩, ⟨.cone .point, _⟩, ⟨.cone .point, _, _⟩, e => e

      -- start point of a segment
      | ⟨.point, _⟩, ⟨.cone .point, _⟩, ⟨.base .point, _, _⟩, e => e
      -- end point of a segment
      | ⟨.point, _⟩, ⟨.cone .point, _⟩, ⟨.tip .point, _, _⟩, e => e+1
      | _, _, _, _ => absurd (a := Nonempty Empty) sorry_proof sorry_proof /- `e` is element of Empty -> contradiction, how to prove this? -/

    face_comp := sorry_proof
  }


  instance : LineSet.Coface where
    CofaceIndex :=
      λ {Q} _ P =>
      match Q, P with
      -- neighbours of a point
      | ⟨.point, _⟩, ⟨.point, _⟩ => Unit
      | ⟨.point, _⟩, ⟨.cone .point, _⟩ => Fin 2
      | ⟨.point, _⟩, _ => Empty

      -- neighbours of a segment
      | ⟨.cone .point, _⟩, ⟨.cone .point, _⟩ => Unit
      | ⟨.cone .point, _⟩, _ => Empty

      -- all the rest is empty
      | _, _ => Empty

    coface :=
      λ {Q} e P id =>
      match Q, P with
      -- neighbours of a point
      | ⟨.point, _⟩, ⟨.point, _⟩ =>
        (⟨.point, sorry_proof, sorry_proof⟩, e)
      | ⟨.point, _⟩, ⟨.cone .point, _⟩ =>
        let e : Int := e
        if id = 0
        then (⟨.tip .point, sorry_proof, sorry_proof⟩, e-1)
        else (⟨.base .point, sorry_proof, sorry_proof⟩, e)

      -- neighbours of a segment is the segment itself
      | ⟨.cone .point, _⟩, ⟨.cone .point, _⟩ =>
        (⟨.cone .point, sorry_proof, sorry_proof⟩, e)
      | _, _ => absurd (a := Nonempty Empty) sorry_proof sorry_proof /- `e` is element of Empty -> contradiction, how to prove this? -/

    face_coface := sorry_proof


  instance (P : Prism) : Iterable (LineSet.Elem P) :=
    match P with
    | ⟨.point, _⟩ => by simp[PrismaticSet.Elem, LineSet]; infer_instance
    | ⟨.cone .point, _⟩ => by simp[PrismaticSet.Elem, LineSet]; infer_instance
    | _ =>
      let enum : Enumtype Empty := by infer_instance
      cast sorry_proof enum


  instance (Q P) (e : LineSet.Elem Q) : Enumtype (LineSet.CofaceIndex e P) :=
     match Q, P with
     -- neighbours of a point
     | ⟨.point, _⟩, ⟨.point, _⟩ => by simp[LineSet, PrismaticSet.Coface.CofaceIndex, PrismaticSet.CofaceIndex]; infer_instance
     | ⟨.point, _⟩, ⟨.cone .point, _⟩ => by simp[LineSet, PrismaticSet.Coface.CofaceIndex, PrismaticSet.CofaceIndex]; infer_instance

     -- neighbours of a Circle
     | ⟨.cone .point, _⟩, ⟨.cone .point, _⟩ => by simp[LineSet, PrismaticSet.Coface.CofaceIndex, PrismaticSet.CofaceIndex]; infer_instance

     -- all the rest is empty
     | _, _ =>
       let enum : Enumtype Empty := by infer_instance
       cast sorry_proof enum


  def LineMesh : PrismaticMesh ℝ :=
    PrismaticMesh.mk LineSet
      (toPos := λ p =>
        match p with
        | ⟨⟨.point, _⟩, e, _⟩ => (reduce_type_of e)
        | ⟨⟨.cone .point, _⟩, e, x⟩ =>
          let e : Int := e
          let x : ℝ := x
          e + x
        | _ => absurd (a:=True) sorry_proof sorry_proof)


      (toPos_face := sorry_proof)


  instance : LineMesh.ClosestPoint where
      closestPoint := λ x =>
        let nx : Int :=
          if 0 ≤ x
          then  (Float.floor  x.toFloat).toUInt64.toNat
          else -(Float.ceil (-x.toFloat)).toUInt64.toNat
        let ix := x - nx
        if ix = 0 then
          ⟨Prism.point, nx, 0⟩
        else
          let ix : ℝ^{1} := λ [i] => ix
          ⟨Prism.segment, nx, ix⟩
      closestPoint_toPos := sorry_proof
