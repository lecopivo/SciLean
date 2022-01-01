import SciLean.Mathlib.Data.Enumtype
import SciLean.Algebra.Real

namespace SciLean

inductive Prism where
  | point : Prism
  | cone (P : Prism) : Prism
  | prod (P Q : Prism) : Prism

namespace Prism

  def beq (P Q : Prism) : Bool :=
    match P, Q with
    | point, point => true
    | cone P, cone Q => beq P Q
    | prod P P', prod Q Q' => beq P Q ∧ beq P' Q'
    | _, _ => false

  def faceCount (P : Prism) (n : Nat) : Nat :=
    match P with
    | point => if n == 0 then 1 else 0
    | cone P => 
      match n with
      | 0   => 1 + P.faceCount 0
      | n+1 => P.faceCount n + P.faceCount (n+1)
    | prod P Q => ∑ i : Fin (n+1), (P.faceCount i.1) * (Q.faceCount (n-i.1))

  def dim : (P : Prism) → Nat
    | point => 0
    | cone P' => 1 + P'.dim
    | prod P' Q' => P'.dim + Q'.dim

  inductive Face : Prism → Nat → Type where
    | point : Face point 0
    | tip (P : Prism) : Face (cone P) 0
    | cone {n} {P : Prism} (f : Face P n) : Face (cone P) (n+1)
    | base {n} {P : Prism} (f : Face P n) : Face (cone P) n
    | prod {n m} {P Q : Prism} (f : Face P n) (g : Face Q m) 
      : Face (prod P Q) (n + m)

  def Face.beq {P n} (f g : Face P n) : Bool :=
    match P, n, f, g with
    | _, _, point, point => true
    | _, _, tip _, tip _ => true
    | _, _, cone f, cone g => beq f g
    | _, _, base f, base g => beq f g
    | Prism.prod P' Q', _, prod f f', g => sorry -- TODO: This needs to be completed!!!
    | _, _, _, _ => false

  instance {P n} : DecidableEq (Face P n) :=
    λ f g =>
      if f.beq g then (isTrue sorry) else (isFalse sorry)

  def Face.toPrism {P n} (f : Face P n) : Prism :=
    match f with
    | point => Prism.point
    | tip P  => Prism.point
    | cone f => Prism.cone f.toPrism
    | base f => f.toPrism
    | prod f g => Prism.prod f.toPrism g.toPrism

  def Face.ofFace' {P Q : Prism} {n m : Nat} 
    (f : Face P n) (g : Face Q m) (h : f.toPrism = Q) 
    : Face P m 
    :=
      match f, g, h with 
      |   point,   point, _ => point
      |  tip P',   point, _ => tip P'
      | cone f',   tip _, _ => tip _
      | cone f', cone g', h => 
        cone (ofFace' f' g' (by simp[toPrism] at h; apply h))
      | cone f', base g', h => 
        base (ofFace' f' g' (by simp[toPrism] at h; apply h))
      | base f',      g', h => 
        base (ofFace' f' g' (by simp[toPrism] at h; apply h))
      | prod f' f'', prod g' g'', h => 
        prod (ofFace' f' g' (by simp[toPrism] at h; apply h.1)) 
             (ofFace' f'' g'' (by simp[toPrism] at h; apply h.2))

  def Face.ofFace {P n m} {f : Face P n} (g : Face (f.toPrism) m) : Face P m
    := ofFace' f g (by rfl)

  def first (P : Prism) (n : Nat) : Option (Face P n) :=
    match P, n with
    | point, 0 => some Face.point
    | point, _ => none
    | cone P', 0 => Face.tip P'
    | cone P', n'+1 => 
      match first P' n' with
      | some f => some (Face.cone f)
      | none => none
    | Prism.prod P' Q', n =>
      Id.run do
      for i in [0:n+1] do
        match first P' i, first Q' (n-i) with
        | some f', some g' =>
          return (some ((sorry : i+(n-i)=n) ▸ Face.prod f' g'))
        | _, _ => continue
      none

  def Face.next {P n} (f : Face P n) : Option (Face P n) := 
    match P, n, f with
    | Prism.point, 0, point => none
    | Prism.cone P', 0, tip _ => 
      match first P' 0 with
      | some f' => some (base f')
      | none => none
    | Prism.cone P', n'+1, cone f' => 
      match next f' with
      | some f'' => some (cone f'')
      | none => 
        match first P' (n'+1) with
        | some f'' => some (base f'')
        | none => none
    | Prism.cone P', _, base f' => 
      match next f' with
      | some f'' => some (base f'')
      | none => none
    | _, _, @prod n' m' P' Q' f' g' => 
      match next f' with
      | some f'' => some (prod f'' g')
      | none => 
        match first P' n', next g' with
        | some f'', some g'' => some (prod f'' g'')
        | _, _ => 
          match m' with
          | 0 => none
          | m''+1 => 
            match first P' (n'+1), first Q' m'' with
            | some f'', some g'' => some ((sorry : (n'+1)+m'' = n'+(m''+1)) ▸ prod f'' g'')
            | _, _ => none

  instance {P n} : Iterable (Face P n) :=
  {
    first := first P n
    next := Face.next
    decEq := by infer_instance
  }
  

  def Face.toFin {P n} (f : Face P n) : Fin (P.faceCount n) := 
    match P, n, f with
    | _, _, point => ⟨0, sorry⟩
    | _, _, tip _ => ⟨0, sorry⟩
    | _, _, cone f' => ⟨f'.toFin.1, sorry⟩
    | Prism.cone P', 0, base f' => ⟨1+f'.toFin.1, sorry⟩
    | Prism.cone P', n'+1, base f' => ⟨(P'.faceCount n')+f'.toFin.1, sorry⟩
    | _, _, @prod n' m' P' Q' f' g' => 
      ⟨(∑ i : Fin n', (P'.faceCount i)*(Q'.faceCount (n-i)))
       + f'.toFin.1 + g'.toFin.1 * (P'.faceCount n'), sorry⟩
      
  def Face.fromFin (P : Prism) (n : Nat) (i : Fin (P.faceCount n)) : Face P n := sorry

#check Nat
  def segment  := cone point
  def triangle := cone segment
  def square   := prod segment segment
  def tet      := cone triangle
  def cube     := prod segment square
  def pyramid  := cone square
  def prism    := prod segment triangle

  #eval (
    (do
      let mut it := first prism 2
      for i in [0:100] do
        match it with
        | some f => do
          IO.print s!"{f.toFin}: "
          let mut jt := first f.toPrism 0
          for j in [0:100] do
            match jt with
            | some g => 
              IO.print s!"{g.ofFace.toFin} "
              jt := g.next
            | none => break
          IO.println ""
          it := f.next
        | none => break
    ) : IO Unit)

  -- Natural embedding space
  def E : (P : Prism) → Type
    | point => Unit
    | cone P' => ℝ × P'.E
    | prod P' Q' => P'.E × Q'.E

  def pointCount (P : Prism) : Nat := P.faceCount 0

  def pos' {P : Prism} : Face P 0 → P.E := sorry
  -- def pos {P : Prism} : Fin (P.pointCount) → ℝ^P.dim := sorry

  -- def toRn : {P : Prism} → P.E → ℝ^P.dim := sorry
  -- def fromRn : {P : Prism} → ℝ^P.dim → P.E := sorry

  def barycentricCoord' {P : Prism} : Face P 0 → P.E → ℝ := sorry
  -- def barycentricCoord {P : Prism} : Fin (P.pointCount) → ℝ^P.dim → ℝ := sorry

  -- embedding map from a face to prism
  def Face.embed {P n} (f : Face P n) : f.toPrism.E → P.E := sorry

  

  -- order preserving map from one prism to another prism
  -- Should include pure inclusions like Face but also collapses
  -- 
  -- There is some non-uniqueness, doing `shift` if the same as `cone ∘ base`
  inductive Morph : Prism → Type
    | point : Morph point
    | tip (P : Prism) : Morph (cone P)
    | cone {P : Prism} (f : Morph P) : Morph (cone P)
    | base {P : Prism} (f : Morph P) : Morph (cone P)
    | collapse {P : Prism} (m : Morph (cone P)) : Morph (cone (cone P))
    | shift    {P : Prism} (m : Morph (cone P)) : Morph (cone (cone P))
    | prod {P Q : Prism} (f : Morph P) (g : Morph Q) : Morph (prod P Q)

  -- Face if Morph not containing collapses and shifts
