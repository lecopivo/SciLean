module

public import SciLean.Data.Mesh.PrismaticMesh

@[expose] public section


namespace SciLean

  def CircleSet (n : Nat) : PrismaticSet :=
  {
    Elem := λ P =>
      match P with
      | ⟨.point, _⟩ => Fin n
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
      | ⟨.point, _⟩, ⟨.cone .point, _⟩, ⟨.tip .point, _, _⟩, e => ⟨(e.1+1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt e.2)⟩
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

  instance : (CircleSet n).Coface where
    CofaceIndex :=
      λ {Q} _ P =>
      match Q, P with
      -- neighbours of a point
      | ⟨.point, _⟩, ⟨.point, _⟩ => Unit
      | ⟨.point, _⟩, ⟨.cone .point, _⟩ =>
        match n with
        | 0 => Empty
        | 1 => Unit
        | _+2 => Fin 2

      -- neighbours of a segment
      | ⟨.cone .point, _⟩, ⟨.cone .point, _⟩ => Unit

      -- all the rest is empty
      | _, _ => Empty

    coface :=
      λ {Q} e P id =>  -- Q.nrepr = f'.toPrism.toCanonical
      match Q, P with
      -- neighbours of a point
      | ⟨.point, _⟩, ⟨.point, _⟩ =>
        (⟨.point, rfl, by show PrismRepr.point.toCanonical = .point; rw [PrismRepr.toCanonical]⟩, e)
      | ⟨.point, _⟩, ⟨.cone .point, _⟩ =>
        match hn : n with
        | 0 => absurd (a:= True) trivial (Fin.elim0 e) /- `id` has to be an element of Empty -/
        | 1 => (⟨.base .point, rfl, by show PrismRepr.point.toCanonical = .point; rw [PrismRepr.toCanonical]⟩, ⟨0,Nat.one_pos⟩)
        | n'+2 =>
            let e : Fin (n'+2) := e
            if id = 0
            then (⟨ .tip .point, rfl, by show PrismRepr.point.toCanonical = .point; rw [PrismRepr.toCanonical]⟩, ⟨(e+n-1) % n, by rw [hn]; exact Nat.mod_lt _ (Nat.succ_pos _)⟩)
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


  instance (n : Nat) (P : Prism) : Enumtype ((CircleSet n).Elem P) :=
    match P with
    | ⟨.point, _⟩ => by simp[PrismaticSet.Elem, CircleSet]; infer_instance
    | ⟨.cone .point, _⟩ => by simp[PrismaticSet.Elem, CircleSet]; infer_instance
    | _ =>
      let enum : Enumtype Empty := by infer_instance
      cast sorry_proof enum

  instance (n Q P) (e : (CircleSet n).Elem Q) : Enumtype ((CircleSet n).CofaceIndex e P) :=
     match Q, P with
     -- neighbours of a point
     | ⟨.point, _⟩, ⟨.point, _⟩ => by simp[CircleSet, PrismaticSet.CofaceIndex, PrismaticSet.Coface.CofaceIndex]; infer_instance
     | ⟨.point, _⟩, ⟨.cone .point, _⟩ =>
       match n with
       | 0 => by simp[CircleSet, PrismaticSet.CofaceIndex, PrismaticSet.Coface.CofaceIndex]; infer_instance
       | 1 => by simp[CircleSet, PrismaticSet.CofaceIndex, PrismaticSet.Coface.CofaceIndex]; infer_instance
       | n'+2 => by simp[CircleSet, PrismaticSet.CofaceIndex, PrismaticSet.Coface.CofaceIndex]; infer_instance

     -- neighbours of a Circle
     | ⟨.cone .point, _⟩, ⟨.cone .point, _⟩ => by simp[CircleSet, PrismaticSet.CofaceIndex, PrismaticSet.Coface.CofaceIndex]; infer_instance

     -- all the rest is empty
     | _, _ =>
       let enum : Enumtype Empty := by infer_instance
       cast sorry_proof enum


  def CircleMesh (n : Nat) : PrismaticMesh (ℝ×ℝ) :=
    PrismaticMesh.mk (CircleSet n)
      (toPos := λ p =>
        match p with
        | ⟨⟨.point, _⟩, e, x⟩ =>
          let e : Fin n := e
          let θ := 2*Math.pi*e.1.toReal/n
          (Math.cos θ, Math.sin θ)
        | ⟨⟨.cone .point, _⟩, e, x⟩ =>
          let e : Fin n := e
          let x : ℝ := x
          let θ := 2*Math.pi*(e.1.toReal + x)/n
          (Math.cos θ, Math.sin θ)
        | _ => absurd (a:=True) trivial sorry_proof
      )
      (toPos_face := sorry_proof)


  instance : (CircleMesh n).ClosestPoint where
      closestPoint := λ xy =>
        let θ := (Math.atan2 (-xy.2) (-xy.1) + Math.pi)/(2*Math.pi)
        let nθ := (Float.floor θ.toFloat).toUInt64.toNat
        let iθ := θ - nθ
        if iθ = 0 then
          ⟨Prism.point, ⟨nθ, sorry_proof⟩, 0⟩
        else
          let iθ : ℝ^{1} := λ [i] => iθ
          ⟨Prism.segment, ⟨nθ, sorry_proof⟩, iθ⟩

      closestPoint_toPos := sorry_proof
