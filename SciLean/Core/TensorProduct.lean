import SciLean.Mathlib.Convenient.Basic

namespace SciLean

namespace TensorProduct

  variable {X Y} [Vec X] [Vec Y]

  def Repr (X Y : Type) := Array (X×Y)

  -- TODO: Define equivalence of two formal sums `∑ i, x i ⊗ y i`
  def Equiv (u v : Repr X Y) : Prop := sorry

end TensorProduct

-- Algebraic tensor product
-- If I'm not mistaken, for X Y convenient vector spaces, the algebraic tensor product X ⊗ Y is again a convenient vector space. It is not some completion of the algebraic tensor product.
-- TODO: make this as Graded Quotient
def TensorProduct (X Y : Type) [Vec X] [Vec Y] : Type := Quot (TensorProduct.Equiv (X:=X) (Y:=Y))

namespace TensorProduct

  def tprod {X Y} [Vec X] [Vec Y] (x : X) (y : Y) : TensorProduct X Y := Quot.mk _ #[(x,y)]

  instance {X Y} [Vec X] [Vec Y] : OTimes X Y (TensorProduct X Y) := ⟨⟩
  instance {X Y} [Vec X] [Vec Y] (x : X) (y : Y) : OTimes x y (tprod x y) := ⟨⟩

  variable {X Y Z} [Vec X] [Vec Y] [Vec Z]

  open Classical in
  noncomputable
  def repr  (xy : X ⊗ Y)
    : (n : Nat) × (Fin n → X) × (Fin n → Y) :=
      let r : Array (X×Y) := choose (Quot.exists_rep xy)
      let n := r.size
      let x := λ i => r[i].1
      let y := λ i => r[i].2
      ⟨n,x,y⟩

  structure is_linear  (f : X → Y) : Prop where
    add  : ∀ x y, f (x + y) = f x + f y
    smul : ∀ (s : ℝ) x, f (s•x) = s • (f x)

  /-- Extends bilinear map `X → Y → Z` to `X ⊗ Y → Z`. -/
  def map' (f : X → Y → Z) (h : is_linear f ∧ ∀ x, is_linear (f x)) (xy : X ⊗ Y) : Z :=
    Quot.lift (λ xy : Array (X×Y) => ∑ i : Idx xy.size.toUSize, (f (xy.uget i.1 sorry).1 (xy.uget i.1 sorry).2)) sorry_proof xy

  @[simp] theorem map'_tprod (f : X → Y → Z) (h : is_linear f ∧ ∀ x, is_linear (f x)) (x : X) (y : Y)
    : map' f h (x⊗y) = f x y := sorry_proof

  instance : Neg (X⊗Y) := ⟨λ xy  => 
    xy.liftOn (λ xy : Array (X×Y) => Quot.mk _ <| xy.map (λ (x,y) => (-x,y))) sorry_proof⟩

  instance : Add (X⊗Y) := ⟨λ xy xy' => 
    xy.liftOn (λ xy : Array (X×Y) => 
    xy'.liftOn (λ xy' : Array (X×Y) => Quot.mk _ (xy.append xy')) sorry_proof) sorry_proof⟩

  instance : Sub (X⊗Y) := ⟨λ xy xy' => xy + (-xy')⟩

  -- We scale x and y by the same amount in the hope of better numerical stability
  instance : SMul ℝ (X⊗Y) := ⟨λ r xy => 
    let s  := if 0 ≤ r then 1 else 0
    let r' := if 0 ≤ r then r.sqrt else (-r).sqrt 
    xy.liftOn (λ xy =>
      Quot.mk _ <| xy.map (λ (x,y) => ((s*r')•x, r'•y))) sorry_proof⟩

  instance : Zero (X⊗Y) := ⟨(Quot.mk _ (#[] : Array (X×Y)))⟩

  instance : Vec (X⊗Y) := Vec.mkSorryProofs
