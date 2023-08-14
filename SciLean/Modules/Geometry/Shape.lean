import SciLean.Core.Defs
import SciLean.Core.Diff

namespace SciLean


class LieGroup.SO (G V : Type) [SemiHilbert V] [Group G] extends DistribMulAction G V -- extends Diff G


/--
Shape parametrized by `P` living in `X`
-/
structure Shape {P X} (toSet : P → Set X) where
  params : P  
  -- add some niceness properties 
  --  - probably that it is a closed set
  --  - compactness is probably too restrictive

namespace Shape

  -- TODO: replace all occurrences of `p` to `toSet`
  variable {P X : Type} [Hilbert X] {p : P → Set X} {toSet : P → Set X}

  ------------------------------------------------------------------------------
  -- Locate
  ------------------------------------------------------------------------------
  inductive Location | inside | boundary | outside 
  deriving Inhabited, BEq, Repr

  noncomputable 
  def locateSpec (s : Shape p) (x : X) : Location := sorry
    -- if x ∈ interior s then
    --   inside
    -- else if x ∈ univ ∖ closure s
    --   outside
    -- else
    --   boundary

  class IsLocate (f : Shape p → X → Location) : Prop where
    is_locate : locateSpec = f

  class HasLocate (p : P → Set X) where
    locate : Shape p → X → Location
    is_locate : IsLocate locate

  def locate [HasLocate p] (s : Shape p) (x : X) := HasLocate.locate s x

  instance [HasLocate p] : IsLocate (locate (p:=p)) := HasLocate.is_locate 
  @[simp] theorem locate_spec [IsLocate f]
    : locateSpec = f := IsLocate.is_locate

  ------------------------------------------------------------------------------
  -- Level Set 
  ------------------------------------------------------------------------------
  class IsLevelSet (f : Shape p → X → ℝ) : Prop where
    is_level_set : ∀ (s : Shape p), 
      if 0 < f s x then
        s.locateSpec x = outside
      else if f s x = 0 then
        s.locateSpec x = boundary
      else 
        s.locateSpec x = inside

  class HasLevelSet (p : P → Set X) where
    levelSet : Shape p → X → ℝ
    is_level_set : IsLevelSet levelSet

  def levelSet [HasLevelSet p] (s : Shape p) (x : X) := HasLevelSet.levelSet s x

  instance [HasLevelSet p] : IsLevelSet (levelSet (p:=p)) := HasLevelSet.is_level_set

  def locateFromLevelSet [HasLevelSet p] : HasLocate p := 
  {
    locate := λ s x =>
      let d := s.levelSet x
      if 0 < d then
        .outside
      else if d = 0 then
        .boundary
      else
        .inside
    is_locate := sorry_proof
  }


  ------------------------------------------------------------------------------
  -- Signed Distance Function
  ------------------------------------------------------------------------------
  -- TODO: This should map to `ℝ∪{∞}∪{-∞}` to allow for empty space and total space
  noncomputable 
  def sdfSpec (s : Shape p) (x : X) : ℝ := sorry
    -- match s.locateSpec with
    -- | inside => - dist(x, boundary s)
    -- | outside =>  dist(x, boundary s)
    -- | boundary => 0

  class IsOutsideDist (f : Shape p → X → ℝ) : Prop where
    is_outside_dist : ∀ s x,
      0 ≤ f s x → s.sdfSpec x = f s x

  class IsInsideDist (f : Shape p → X → ℝ) : Prop where
    is_inside_dist : ∀ s x,
      f s x ≤ 0 → s.sdfSpec x = f s x

  class IsSdf (f : Shape p → X → ℝ) extends IsOutsideDist f, IsInsideDist f : Prop

  class HasSdf (p : P → Set X) where
    sdf (s : Shape p) (x : X) : ℝ
    is_sdf : IsSdf sdf
  
  def sdf [HasSdf p] (s : Shape p) (x : X) := HasSdf.sdf s x

  instance [HasSdf p] : IsSdf (sdf (p:=p)) := HasSdf.is_sdf
  instance (f : Shape p → X → ℝ) [IsSdf f] : IsLevelSet f := sorry

  @[simp] theorem sdf_spec (f : Shape p → X → ℝ) [IsSdf f]
    : sdfSpec = f := sorry_proof

  def locateFromSdf [HasSdf p] : HasLocate p := 
  {
    locate := λ s x =>
      let d := s.sdf x
      if 0 < d then
        .outside
      else if d = 0 then
        .boundary
      else
        .inside
    is_locate := sorry_proof
  }


  ------------------------------------------------------------------------------
  -- Closest Point
  ------------------------------------------------------------------------------
  /--
  Finds a closest point on the boundary of `s` to the point `x` and also tells you if 
  `x` is inside/outside or on the boundary of `s`.
  If the closest point is not unique, it will just pick one.
  -/
  class HasClosestPoint (toSet : P → Set X) where
    closestPointLoc (s : Shape toSet) (x : X) : (Option X) × Location
    is_closest_point : (sorry : Prop)

  def closestPoint [HasClosestPoint toSet] (s : Shape toSet) (x : X) : Option X := 
    (HasClosestPoint.closestPointLoc s x).1

  def closestPointLoc [HasClosestPoint toSet] (s : Shape toSet) (x : X) : (Option X) × Location := 
    HasClosestPoint.closestPointLoc s x

  
  ------------------------------------------------------------------------------
  -- Shape Transform
  ------------------------------------------------------------------------------
  class HasTransform (toSet : P → Set X) (f : X → X) where
    trans : P → P
    is_trans : ∀ p x, x ∈ toSet p ↔ f x ∈ toSet (trans p)

  def trans (f : X → X) [HasTransform p f] (s : Shape p) : Shape p := ⟨HasTransform.trans p f s.params⟩

  -- Common transformations
  abbrev HasReflect (p : P → Set X) := HasTransform p Neg.neg
  abbrev HasTranslate (p : P → Set X) := ∀ t, HasTransform p λ x => x + t
  abbrev HasRotate (R : Type) [Group R] [LieGroup.SO R X] (p : P → Set X)  
    := ∀ r : R, HasTransform p λ x => r • x
  abbrev HasScale (p : P → Set X)  
    := ∀ s : ℝ, HasTransform p λ x => s • x
  abbrev HasMirror (p : P → Set X) := ∀ n : X, HasTransform p λ x => x - ((2 : ℝ) * ⟪x,n⟫) • n

  abbrev reflect [HasReflect p] (s : Shape p) := s.trans Neg.neg
  abbrev translate [HasTranslate p] (s : Shape p) (t : X) := s.trans λ x => x + t
  abbrev rotate {R : Type} [Group R] [LieGroup.SO R X] [HasRotate R p]
    (s : Shape p) (r : R) := s.trans λ x => r • x 
  abbrev scale [HasScale p] (s : Shape p) (r : ℝ) := s.trans λ x => r • x 
  abbrev mirror [HasMirror p] (s : Shape p) (n : X) := s.trans λ x => x - ((2 : ℝ) * ⟪x,n⟫) • n


  ------------------------------------------------------------------------------
  -- Minkowski Sum
  ------------------------------------------------------------------------------
  class HasMinkowskiSum (toSet₁ : P → Set X) (toSet₂ : Q → Set X) (toSet₃ : outParam $ R → Set X) where
    sum : P → Q → R
    is_sum : ∀ p q z, 
      (z ∈ toSet₃ (sum p q)) 
      ↔ 
      ∃ (x y : X), (z = x + y) ∧ (x ∈ toSet₁ p) ∧ (y ∈ toSet₂ q)


  ------------------------------------------------------------------------------
  -- Distance between two shapes
  ------------------------------------------------------------------------------
  noncomputable
  def distSpec (A : Shape p) (B : Shape q) : ℝ := sorry
    -- evaluate signed distance of minkowski sum of A,-B at the origin

  class HasDist (p : P → Set X) (q : Q → Set X) where
    dist (A : Shape p) (B : Shape q) : ℝ 
    is_dist : ∀ A B, distSpec A B = dist A B

  def dist [HasDist p q] (A : Shape p) (B : Shape q) : ℝ := HasDist.dist A B
  @[simp] theorem dist_spec [HasDist p q] (A : Shape p) (B : Shape q)
    : distSpec A B = dist A B := by apply HasDist.is_dist

  

  -- Transformed Shapes
  ------------------------------------------------------------------------------        

  ------------------------------------------------------------------------------
  -- Translated Shape
  ------------------------------------------------------------------------------        
  structure TranslatedParams (P : Type) (X : Type) where
    params : P
    translate : X

  def translatedSet (toSet : P → Set X) 
    : TranslatedParams P X → Set X :=
    λ ⟨p, t⟩ x => (x - t) ∈ toSet p

  def mkTranslated (t : X) (s : Shape toSet) : Shape (translatedSet toSet) :=
  {
    params := {
      params := s.params
      translate := t
    }
  }

  instance 
    : HasTranslate (translatedSet toSet) := λ t' => 
  {
    trans := λ ⟨p, t⟩ => ⟨p, t + t'⟩
    is_trans := sorry
  }

  instance (R : Type) [Group R] [LieGroup.SO R X] [HasRotate R toSet]
    : HasRotate R (translatedSet toSet) := λ r => 
  {
    trans := λ ⟨p, t⟩ =>
      let s : Shape toSet := ⟨p⟩
      ⟨(s.rotate r).1, r • t⟩
    is_trans := sorry
  }

  instance [HasScale toSet]
    : HasScale (translatedSet toSet) := λ r => 
  {
    trans := λ ⟨p, t⟩ =>
      let s : Shape toSet := ⟨p⟩
      ⟨(s.scale r).1, r • t⟩
    is_trans := sorry
  }

  instance [HasLocate toSet]
    : HasLocate (translatedSet toSet) where
    locate := λ ⟨p, t⟩ x => 
      let s' : Shape toSet := ⟨p⟩
      let x' := x - t
      s'.locate x'
    is_locate := sorry

  instance [HasLevelSet toSet]
    : HasLevelSet (translatedSet toSet) where
    levelSet := λ ⟨p, t⟩ x => 
      let s' : Shape toSet := ⟨p⟩
      let x' := x - t
      s'.levelSet x'
    is_level_set := sorry

  instance [HasSdf toSet]
    : HasSdf (translatedSet toSet) where
    sdf := λ ⟨p, t⟩ x => 
      let s' : Shape toSet := ⟨p⟩
      let x' := x - t
      s'.sdf x'
    is_sdf := sorry

  instance  [HasClosestPoint toSet] 
    : HasClosestPoint (translatedSet toSet) where
    closestPointLoc := λ ⟨p, t⟩ x => 
      let s' : Shape toSet := ⟨p⟩
      let x' := x - t
      let (cp?, loc) := s'.closestPointLoc x'
      (cp?.map λ cp => cp + t, loc)
    is_closest_point := sorry


  ------------------------------------------------------------------------------
  -- Rotated Shape
  ------------------------------------------------------------------------------        
  structure RotatedParams (P : Type) (X R : Type) [Hilbert X] [Group R] [LieGroup.SO R X] where
    params : P
    rotate : R
    inverseRotate : R
    valid_rotate : rotate * inverseRotate = 1

  def rotatedSet (R : Type) [Hilbert X] [Group R] [LieGroup.SO R X] (toSet : P → Set X) 
    : RotatedParams P X R → Set X :=
    λ ⟨p, _, ir, _⟩ x => ir • x ∈ toSet p

  def mkRotateded {R : Type} [Group R] [LieGroup.SO R X] (r : R) (s : Shape toSet)
    : Shape (rotatedSet R toSet) :=
    {
      params := {
        params := s.params
        rotate := r
        inverseRotate := r⁻¹
        valid_rotate := by simp
      }
    }
  
  instance (R : Type) [Group R] [LieGroup.SO R X] [HasTranslate toSet]
    : HasTranslate (rotatedSet R toSet) := λ t => 
  {
    trans := λ ⟨p, r, ir, h⟩ => 
      let s' : Shape toSet := ⟨p⟩ 
      let p' := (s'.translate (ir•t)).1
      ⟨p', r, ir, h⟩
    is_trans := sorry
  }

  instance (R : Type) [Group R] [LieGroup.SO R X] 
    : HasRotate R (rotatedSet R toSet) := λ r' => 
  {
    trans := λ ⟨p, r, ir, h⟩ => ⟨p, r' * r, ir * r'⁻¹, sorry⟩
    is_trans := sorry
  }

  instance (R : Type) [Group R] [LieGroup.SO R X] [HasScale toSet]
    : HasScale (rotatedSet R toSet) := λ r' => 
  {
    trans := λ ⟨p, r, ir, h⟩ => 
      let s' : Shape toSet := ⟨p⟩ 
      let p' := (s'.scale r').1
      ⟨p', r, ir, h⟩
    is_trans := sorry
  }

  instance (R : Type) [Group R] [LieGroup.SO R X] [HasLocate toSet] 
    : HasLocate (rotatedSet R toSet) where
    locate := λ ⟨p, r, ir, _⟩ x => 
      let x' := ir • x
      let s' : Shape toSet := ⟨p⟩
      s'.locate x'
    is_locate := sorry

  instance (R : Type) [Group R] [LieGroup.SO R X] [HasLevelSet toSet] 
    : HasLevelSet (rotatedSet R toSet) where
    levelSet := λ ⟨p, r, ir, _⟩ x => 
      let x' := ir • x
      let s' : Shape toSet := ⟨p⟩
      s'.levelSet x'
    is_level_set := sorry

  instance (R : Type) [Group R] [LieGroup.SO R X] [HasSdf toSet] 
    : HasSdf (rotatedSet R toSet) where
    sdf := λ ⟨p,  _, ir, _⟩ x => 
      let x' := ir • x
      let s' : Shape toSet := ⟨p⟩
      s'.sdf x'
    is_sdf := sorry

  instance (R : Type) [Group R] [LieGroup.SO R X] [HasClosestPoint toSet] 
    : HasClosestPoint (rotatedSet R toSet) where
    closestPointLoc := λ ⟨p, r, ir, _⟩ x => 
      let x' := ir • x 
      let s' : Shape toSet := ⟨p⟩
      let (cp?, loc) := s'.closestPointLoc x'
      (cp?.map λ cp => r • cp, loc)
    is_closest_point := sorry


  ------------------------------------------------------------------------------
  -- Rigid Transform 
  ------------------------------------------------------------------------------        
  structure RigidTransformParams (P : Type) (X R : Type) [Hilbert X] [Group R] [LieGroup.SO R X] where
    params : P
    translate : X
    rotate : R
    inverseRotate : R
    valid_rotate : rotate * inverseRotate = 1

  def rigidTransformSet (R : Type) [Hilbert X] [Group R] [LieGroup.SO R X] (toSet : P → Set X) 
    : TranslatedParams (RotatedParams P X R) X → Set X := translatedSet (rotatedSet R toSet)

  def mkRigidTransformed {R : Type} [Group R] [LieGroup.SO R X] (t : X) (r : R) (s : Shape toSet)
    : Shape (rigidTransformSet R toSet) := s.mkRotateded r |>.mkTranslated t
  
  instance (R : Type) [Group R] [LieGroup.SO R X]
    : HasTranslate (rigidTransformSet R toSet) := by unfold rigidTransformSet; infer_instance

  instance (R : Type) [Group R] [LieGroup.SO R X] 
    : HasRotate R (rigidTransformSet R toSet) := by unfold rigidTransformSet; infer_instance

  instance (R : Type) [Group R] [LieGroup.SO R X] [HasScale toSet]
    : HasScale (rigidTransformSet R toSet) := by unfold rigidTransformSet; infer_instance

  instance (R : Type) [Group R] [LieGroup.SO R X] [HasLocate toSet] 
    : HasLocate (rigidTransformSet R toSet) := by unfold rigidTransformSet; infer_instance

  instance (R : Type) [Group R] [LieGroup.SO R X] [HasLevelSet toSet] 
    : HasLevelSet (rigidTransformSet R toSet) := by unfold rigidTransformSet; infer_instance

  instance (R : Type) [Group R] [LieGroup.SO R X] [HasSdf toSet] 
    : HasSdf (rigidTransformSet R toSet) := by unfold rigidTransformSet; infer_instance

  instance (R : Type) [Group R] [LieGroup.SO R X] [HasClosestPoint toSet] 
    : HasClosestPoint (rigidTransformSet R toSet) := by unfold rigidTransformSet; infer_instance


  ------------------------------------------------------------------------------
  -- Velocity Sweep 
  ------------------------------------------------------------------------------
  structure VelSweepParams (P : Type) (X : Type) [Vec X] where
    params : P
    t₁ : ℝ
    t₂ : ℝ
    vel  : X
    
  def velSweepSet (toSet : P → Set X) : VelSweepParams P X → Set (ℝ × X) :=
    λ p (t,x) => 
      p.t₁ ≤ t ∧ t ≤ p.t₂ 
      ∧ 
      x - (t - p.t₁)•p.vel ∈ toSet p.params

  def mkVelSweep (t₁ t₂ : ℝ) (vel : X) (s : Shape toSet)
    : Shape (velSweepSet toSet) :=
    {
      params := { 
        params := s.params
        t₁ := t₁
        t₂ := t₂
        vel := vel
      }
    }

  instance {toSet : P → Set X} [HasLocate toSet]
    : HasLocate (velSweepSet toSet)
  where
    locate := λ s (t,x) => 
      if s.params.t₁ ≤ t && t ≤ s.params.t₂ then
        let s' : Shape toSet := ⟨s.params.params⟩
        match s'.locate (x - (t - s.params.t₁)•s.params.vel) with
        | .outside => .outside
        | .boundary => .boundary
        | .inside => 
          if t == s.params.t₁ || t == s.params.t₂ then
            .boundary
          else
            .inside
      else
        .outside
    is_locate := sorry

  instance {toSet : P → Set X} [HasClosestPoint toSet]
    : HasClosestPoint (velSweepSet toSet)
  where
    closestPointLoc := λ s (t,x) => 
      let t₁ := s.params.t₁
      let t₂ := s.params.t₂
      let vel := s.params.vel

      if t₂ < t₁ then
        (none, .outside)

      else if t ≤ t₁ then
        let s₁ : Shape toSet := ⟨s.params.params⟩
        let (cp₁?, loc) := s₁.closestPointLoc x
        match cp₁?, loc with
        | some cp₁, .outside  => ((t₁, cp₁) , .outside)
        | some cp₁, .inside   => ((t₁, x) , if t = t₁ then .boundary else .outside)
        | some cp₁, .boundary => ((t₁, x) , if t = t₁ then .boundary else .outside)
        | none, .outside  => (none, .outside)
        | none, .inside   => ((t₁, x), if t = t₁ then .boundary else .outside)
        | none, .boundary => ((t₁, x), if t = t₁ then .boundary else .outside)

      else if t₂ ≤ t then
        let s₁ : Shape toSet := ⟨s.params.params⟩
        let (cp₂?, loc) := s₁.closestPointLoc (x - (t₂-t₁)•vel)
        let cp₂? := cp₂?.map (λ cp => cp + (t₂-t₁)•vel)
        match cp₂?, loc with
        | some cp₂, .outside  => ((t₂, cp₂) , .outside)
        | some cp₂, .inside   => ((t₂, x) , if t = t₂ then .boundary else .outside)
        | some cp₂, .boundary => ((t₂, x) , if t = t₂ then .boundary else .outside)
        | none, .outside  => (none, .outside)
        | none, .inside   => ((t₂, x), if t = t₂ then .boundary else .outside)
        | none, .boundary => ((t₂, x), if t = t₂ then .boundary else .outside)

      else -- now we have `t₁ < t ∧ t < t₂`
        let Δt := t - t₁
        let x₁ := x - Δt•vel
        let s₁ : Shape toSet := ⟨s.params.params⟩
        let (cp₁?,loc₁) := s₁.closestPointLoc x₁

        match cp₁? with
        | none => 
           match loc₁ with
           | .outside => (none, .outside)
           | .inside  => 
             if t - t₁ ≤ t₂ - t then
               ((t₁,x), if t = t₁ then .boundary else .inside)
             else
               ((t₂,x), if t = t₂ then .boundary else .inside)  
           | .boundary => 
             -- if the point `x` is on the boundary then there has to be a closes point
             panic! "Unreachable code in `HasClosestPoint.closestPointLoc`"
        | some cp₁ =>

          -- I want to write thise:
          -- let Δt' := solution Δt', ⟪(x,t) - (cp₁, t₁) - Δt'•(vel,1), (vel,1)⟫ = 0 rewrite_by solve
          let Δt' := (⟪x-cp₁,vel⟫ + Δt) / (‖vel‖² + 1)
          let t'  := t₁ + Δt'
          let cp' := cp₁ + Δt'•vel

          match loc₁ with
          | .boundary => ((t,x) , .boundary)
          | .outside => 
            if t' < t₁ then
              ((t₁, cp₁), .outside)
            else if t₂ < t' then
              ((t₂, cp₁ + (t₂ - t₁)•vel), .outside)
            else
              ((t', cp'), .outside)
          | .inside => 
            let d2' := ‖cp' - x‖² + (t' - t)^2
            let d2₁ := (t-t₂)^2
            let d2₂ := (t₂-t)^2
            if d2₁ ≤ d2' && d2₁ ≤ d2₂ then
              ((t₁, x), .inside)
            else if d2₂ ≤ d2' && d2₂ ≤ d2₁ then
              ((t₂, x + (t₂-t₁)•vel), .inside)
            else
             ((t', cp'), .inside)

    is_closest_point := sorry


end Shape
