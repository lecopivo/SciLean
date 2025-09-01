import SciLean.Data.Mesh.PrismaticMesh

namespace SciLean

  def SegmentSet (n : Nat) : PrismaticSet :=
  {
    Elem := λ P =>
      match P with
      | ⟨.point, _⟩ => Fin (n+1)
      | ⟨.cone .point, _⟩ => Fin n
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

  instance : (SegmentSet n).Coface where
    CofaceIndex :=
      λ {Q} e P =>
      match Q, P with
      -- neighbours of a point
      | ⟨.point, _⟩, ⟨.point, _⟩ => Unit
      | ⟨.point, _⟩, ⟨.cone .point, _⟩ =>
        match n with
        | 0 => Empty
        | n'+1 =>
          let e : Fin (n'+2) := e
          if e = 0 ∨ e = n'+1
          then Unit
          else Fin 2

      -- neighbours of a segment
      | ⟨.cone .point, _⟩, ⟨.cone .point, _⟩ => Unit

      -- all the rest is empty
      | _, _ => Empty

    coface :=
      λ {Q} e P id =>  -- Q.nrepr = f'.toPrism.toCanonical
      match Q, P with
      -- neighbours of a point
      | ⟨.point, _⟩, ⟨.point, _⟩ =>
        (⟨.point, sorry_proof, sorry_proof⟩, e)
      | ⟨.point, _⟩, ⟨.cone .point, _⟩ =>
        match n with
        | 0 => absurd (a:= True) sorry_proof sorry_proof /- `id` has to be an element of Empty -/
        | n'+1 =>
          let e : Fin (n'+2) := e
          if h : e = 0
          then (⟨.base .point, sorry_proof, sorry_proof⟩, ⟨0, sorry_proof⟩)
          else if h' : e = n' + 1
          then (⟨.tip .point, sorry_proof, sorry_proof⟩, ⟨n', by simp⟩)
          else
            let id : Fin 2 := cast (by simp[h,h']) id
            if id = 0
            then (⟨ .tip .point, sorry_proof, sorry_proof⟩, ⟨e-1, sorry_proof⟩)
            else (⟨.base .point, sorry_proof, sorry_proof⟩, ⟨e, sorry_proof⟩)

      -- neighbours of a segment is the segment itself
      | ⟨.cone .point, _⟩, ⟨.cone .point, _⟩ =>
        (⟨.cone .point, sorry_proof, sorry_proof⟩, e)
      | _, _ => absurd (a := Nonempty Empty) sorry_proof sorry_proof /- `e` is element of Empty -> contradiction, how to prove this? -/

    face_coface := sorry_proof


  instance (n : Nat) (P : Prism) : Enumtype ((SegmentSet n).Elem P) :=
    match P with
    | ⟨.point, _⟩ => by simp[PrismaticSet.Elem, SegmentSet]; infer_instance
    | ⟨.cone .point, _⟩ => by simp[PrismaticSet.Elem, SegmentSet]; infer_instance
    | _ =>
      let enum : Enumtype Empty := by infer_instance
      cast sorry_proof enum

  instance (n Q P) (e : (SegmentSet n).Elem Q) : Enumtype ((SegmentSet n).CofaceIndex e P) :=
     match Q, P with
     -- neighbours of a point
     | ⟨.point, _⟩, ⟨.point, _⟩ => by simp[SegmentSet, PrismaticSet.CofaceIndex, PrismaticSet.Coface.CofaceIndex]; infer_instance
     | ⟨.point, _⟩, ⟨.cone .point, _⟩ =>
       match n with
       | 0 => by simp[SegmentSet, PrismaticSet.CofaceIndex, PrismaticSet.Coface.CofaceIndex]; infer_instance
       | n'+1 =>
         let e : Fin (n'+2) := e
         if h : e = 0 ∨ e = n'+1
         then by simp[SegmentSet, PrismaticSet.CofaceIndex, PrismaticSet.Coface.CofaceIndex, h]; infer_instance
         else by simp[SegmentSet, PrismaticSet.CofaceIndex, PrismaticSet.Coface.CofaceIndex, h]; infer_instance
     | ⟨.point, _⟩, _ =>
       let enum : Enumtype Empty := by infer_instance
       cast sorry_proof enum

     -- neighbours of a segment
     | ⟨.cone .point, _⟩, ⟨.cone .point, _⟩ => by simp[SegmentSet, PrismaticSet.CofaceIndex, PrismaticSet.Coface.CofaceIndex]; infer_instance
     | ⟨.cone .point, _⟩, _ =>
       let enum : Enumtype Empty := by infer_instance
       cast sorry_proof enum

     -- all the rest is empty
     | _, _ =>
       let enum : Enumtype Empty := by infer_instance
       cast sorry_proof enum


  def SegmentMesh (n : Nat) : PrismaticMesh ℝ :=
    PrismaticMesh.mk  (SegmentSet n)
      (toPos := λ p =>
        match p with
        | ⟨⟨.point, _⟩, e, x⟩ =>
          let e : Fin (n+1) := e
          e
        | ⟨⟨.cone .point, _⟩, e, x⟩ =>
          let e : Fin n := e
          let x : ℝ := x
          e + x
        | _ => absurd (a:=True) sorry_proof sorry_proof)

      (toPos_face := sorry_proof)


  instance : (SegmentMesh n).ClosestPoint where
      closestPoint := λ x =>
        if x < 0 then
          ⟨Prism.point, ⟨0, sorry_proof⟩, 0⟩
        else if x > n then
          ⟨Prism.point, ⟨n, sorry_proof⟩, 0⟩
        else
          let nx : Nat :=  (Float.floor x.toFloat).toUInt64.toNat
          let ix := x - nx
          if ix = 0 then
            ⟨Prism.point, ⟨nx, sorry_proof⟩, 0⟩
          else
            let ix : ℝ^{1} := λ [i] => ix
            ⟨Prism.segment, ⟨nx, sorry_proof⟩, ix⟩

      closestPoint_toPos := sorry_proof
