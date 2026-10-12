module

public import SciLean.Data.Mesh.PrismaticMesh

@[expose] public section


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
      -- the remaining cases: either `e` is an element of `Empty` or the inclusion `f` is impossible
      | _, ⟨.cone (.cone _), _⟩, _, e | _, ⟨.cone (.prod _ _), _⟩, _, e | _, ⟨.prod _ _, _⟩, _, e => nomatch e
      | _, ⟨.point, _⟩, ⟨.tip _, h₁, h₂⟩, _ | _, ⟨.point, _⟩, ⟨.cone _, h₁, h₂⟩, _
      | _, ⟨.point, _⟩, ⟨.base _, h₁, h₂⟩, _ | _, ⟨.point, _⟩, ⟨.prod _ _, h₁, h₂⟩, _
      | ⟨.cone _, _⟩, ⟨.point, _⟩, ⟨.point, h₁, h₂⟩, _ | ⟨.prod _ _, _⟩, ⟨.point, _⟩, ⟨.point, h₁, h₂⟩, _
      | _, ⟨.cone .point, _⟩, ⟨.point, h₁, h₂⟩, _ | _, ⟨.cone .point, _⟩, ⟨.prod _ _, h₁, h₂⟩, _
      | _, ⟨.cone .point, _⟩, ⟨.tip (.cone _), h₁, h₂⟩, _ | _, ⟨.cone .point, _⟩, ⟨.tip (.prod _ _), h₁, h₂⟩, _
      | _, ⟨.cone .point, _⟩, ⟨.base (.tip _), h₁, h₂⟩, _ | _, ⟨.cone .point, _⟩, ⟨.base (.cone _), h₁, h₂⟩, _
      | _, ⟨.cone .point, _⟩, ⟨.base (.base _), h₁, h₂⟩, _ | _, ⟨.cone .point, _⟩, ⟨.base (.prod _ _), h₁, h₂⟩, _
      | _, ⟨.cone .point, _⟩, ⟨.cone (.tip _), h₁, h₂⟩, _ | _, ⟨.cone .point, _⟩, ⟨.cone (.cone _), h₁, h₂⟩, _
      | _, ⟨.cone .point, _⟩, ⟨.cone (.base _), h₁, h₂⟩, _ | _, ⟨.cone .point, _⟩, ⟨.cone (.prod _ _), h₁, h₂⟩, _
      | ⟨.cone _, _⟩, ⟨.cone .point, _⟩, ⟨.tip .point, h₁, h₂⟩, _ | ⟨.prod _ _, _⟩, ⟨.cone .point, _⟩, ⟨.tip .point, h₁, h₂⟩, _
      | ⟨.cone _, _⟩, ⟨.cone .point, _⟩, ⟨.base .point, h₁, h₂⟩, _ | ⟨.prod _ _, _⟩, ⟨.cone .point, _⟩, ⟨.base .point, h₁, h₂⟩, _
      | ⟨.point, _⟩, ⟨.cone .point, _⟩, ⟨.cone .point, h₁, h₂⟩, _ | ⟨.cone (.cone _), _⟩, ⟨.cone .point, _⟩, ⟨.cone .point, h₁, h₂⟩, _
      | ⟨.cone (.prod _ _), _⟩, ⟨.cone .point, _⟩, ⟨.cone .point, h₁, h₂⟩, _ | ⟨.prod _ _, _⟩, ⟨.cone .point, _⟩, ⟨.cone .point, h₁, h₂⟩, _ =>
        absurd (a := True) trivial (by simp [FaceRepr.ofPrism, FaceRepr.toPrism, PrismRepr.toCanonical] at h₁ h₂)

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
        (⟨.point, rfl, by show PrismRepr.point.toCanonical = .point; rw [PrismRepr.toCanonical]⟩, e)
      | ⟨.point, _⟩, ⟨.cone .point, _⟩ =>
        let e : Int := e
        if id = 0
        then (⟨.tip .point, rfl, by show PrismRepr.point.toCanonical = .point; rw [PrismRepr.toCanonical]⟩, e-1)
        else (⟨.base .point, rfl, by show PrismRepr.point.toCanonical = .point; rw [PrismRepr.toCanonical]⟩, e)

      -- neighbours of a segment is the segment itself
      | ⟨.cone .point, _⟩, ⟨.cone .point, _⟩ =>
        (⟨.cone .point, rfl, by show (PrismRepr.cone .point).toCanonical = .cone .point; rw [PrismRepr.toCanonical, PrismRepr.toCanonical]⟩, e)
      -- the remaining cases, where `id` is an element of `Empty`
      | ⟨.point, _⟩, ⟨.cone (.cone _), _⟩ | ⟨.point, _⟩, ⟨.cone (.prod _ _), _⟩ | ⟨.point, _⟩, ⟨.prod _ _, _⟩
      | ⟨.cone .point, _⟩, ⟨.point, _⟩ | ⟨.cone .point, _⟩, ⟨.cone (.cone _), _⟩
      | ⟨.cone .point, _⟩, ⟨.cone (.prod _ _), _⟩ | ⟨.cone .point, _⟩, ⟨.prod _ _, _⟩
      | ⟨.cone (.cone _), _⟩, _ | ⟨.cone (.prod _ _), _⟩, _ | ⟨.prod _ _, _⟩, _ => nomatch id

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
        | _ => absurd (a:=True) trivial sorry_proof)


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
