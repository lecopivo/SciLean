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
def TensorProduct (X Y : Type) [Vec X] [Vec Y] : Type := Quot (TensorProduct.Equiv (X:=X) (Y:=Y))

namespace TensorProduct

  @[instance]
  axiom instVec {X Y : Type} [Vec X] [Vec Y] : Vec (TensorProduct X Y)

  def tprod {X Y} [Vec X] [Vec Y] (x : X) (y : Y) : TensorProduct X Y := Quot.mk _ #[(x,y)]

  open Lean Elab Term Meta in
  elab x:term:71 "⊗" y:term:72 : term => do
    let xval ← elabTerm x none
    let yval ← elabTerm y none
    let val ← mkAppOptM ``TensorProduct #[xval,yval,none,none] <|> mkAppM ``tprod #[xval,yval]
    pure val

  axiom reprAxiom {X Y : Type} [Vec X] [Vec Y] (xy : X ⊗ Y)
    : ∃ (n : Nat) (x : Fin n → X) (y : Fin n → Y),
      xy = ∑ i, x i ⊗ y i


  open Classical in
  noncomputable
  def repr {X Y : Type} [Vec X] [Vec Y] (xy : X ⊗ Y)
    : (n : Nat) × (Fin n → X) × (Fin n → Y) :=
      let r : Array (X×Y) := choose (Quot.exists_rep xy)
      let n := r.size
      let x := λ i => r[i].1
      let y := λ i => r[i].2
      ⟨n,x,y⟩

  /-- Extends bilinear map `X → Y → Z` to `X ⊗ Y → Z`.

  TODO: Add bilinearity condition on `f` -/
  def extend {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y → Z) (xy : X ⊗ Y) : Z :=
    Quot.lift (λ xy : Array (X×Y) => ∑ i : Fin xy.size, (f xy[i].1 xy[i].2)) sorry xy
