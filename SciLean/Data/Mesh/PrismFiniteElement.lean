import SciLean.Data.Mesh.Prism

namespace SciLean.Prism

  -- Lagrangian DOFs of a given degree and a prism
  inductive LagDOF : (P : Prism) → (deg : Nat) → Type where
    | point (deg : Nat) : LagDOF point deg -- point has only one dof of any degree
    | cone (P : Prism) (deg : Nat) (i : Fin (deg+1)) (dof : LagDOF P i.1) : LagDOF (cone P) deg
    | prod (P Q : Prism) (deg : Nat) (dofP : LagDOF P deg) (dofQ : LagDOF Q deg) : LagDOF (prod P Q) deg

  namespace LagDOF

    def beq {P deg} (d e : LagDOF P deg) : Bool :=
      match d, e with
      | point _, point _ => true
      | cone _ _ i d', cone _ _ j e' => 
        if h : i = j then
          beq d' (h ▸ e')
        else
          false
      | prod _ _ _ dp dq, prod _ _ _ ep eq => 
        beq dp ep ∧ beq dq eq

    instance {P deg} : DecidableEq (LagDOF P deg) :=
      λ f g => if f.beq g then (isTrue sorry) else (isFalse sorry)

    -- Given a DOF on a face of a prism return dof rel to the prism
    def ofFace {P} {deg : Nat} {f : Face P} (dof : LagDOF f.toPrism deg) : LagDOF P deg := sorry

    def zeroDOF (P : Prism) : LagDOF P 0 :=
      match P with
      | Prism.point => point 0
      | Prism.cone P => cone P 0 0 (zeroDOF P)
      | Prism.prod P Q => prod P Q  0 (zeroDOF P) (zeroDOF Q)

    def first (P : Prism) (deg : Nat) : Option (LagDOF P deg) :=
      match P with
      | Prism.point => some $ point deg
      | Prism.cone P => some $ cone P deg (!0) (zeroDOF P)
      | Prism.prod P Q => 
        match first P deg, first Q deg with
        | some dofP, some dofQ => prod P Q deg dofP dofQ
        | _, _ => none -- This case should not happen, maybe panic? or use some confusion

    def next {P deg} (dof : LagDOF P deg) : Option (LagDOF P deg) :=
      match P, dof with
      | _, point _ => none
      | _, cone P deg i dof => 
        match next dof with
        | some dof' => cone P deg i dof'
        | none => 
          if i.1+1 <= deg then
            match first P (i+1) with
            | some dof' => cone P deg (!(i+1)) dof'
            | none => none -- this should not happen
          else 
            none
      | _, prod P Q deg dofP dofQ => 
        match next dofP with
        | some dofP' => prod P Q deg dofP' dofQ
        | none => 
          match first P deg, next dofQ with
          | some dofP', some dofQ' => prod P Q deg dofP' dofQ'
          | _, _ => none
    
    def toPos {P deg} (dof : LagDOF P deg) : P.𝔼 :=
      if deg == 0 then
        P.barycenter
      else 
        match P, dof with
        | _, point d => 0
        | _, cone P deg i dof => 
          let w := (i.1 : ℝ)/(deg : ℝ)
          (1-w, w*dof.toPos)
        | _, prod P Q deg dofP dofQ => 
          (dofP.toPos, dofQ.toPos)



  end LagDOF
