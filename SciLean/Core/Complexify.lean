import SciLean.Core.FinVec
import SciLean.Core.Tactic.FunctionTransformation.Init

namespace SciLean

variable {X Y Z : Type _} [Vec X] [Vec Y] [Vec Z]

-- IsAnalytic 
@[fun_prop_def]
structure IsAnalytic [Vec X] [Vec Y] (f : X → Y)
  -- function is equal to its power series

-- complexify
structure ComplexExtension (X : Type u) where
  real : X
  imag : X

@[fun_trans_def]
noncomputable
def complexify [Vec X] [Vec Y] (f : X → Y) : ComplexExtension X → ComplexExtension Y := sorry

abbrev Complex := ComplexExtension ℝ
notation (priority:=high) "ℂ" => Complex

def conj (x : ComplexExtension X) : ComplexExtension X := ⟨x.real, -x.imag⟩

instance [Add X] : Add (ComplexExtension X)
  := ⟨λ ⟨x1,x2⟩ ⟨y1,y2⟩ => ⟨x1+y1, x2+y2⟩⟩

instance [Sub X]  : Sub (ComplexExtension X)
  := ⟨λ ⟨x1,x2⟩ ⟨y1,y2⟩ => ⟨x1-y1, x2-y2⟩⟩

instance [Neg X] : Neg (ComplexExtension X)
  := ⟨λ ⟨x1,x2⟩ => ⟨-x1, -x2⟩⟩

instance [Add X] [Sub X] [Mul X] : Mul (ComplexExtension X)
  := ⟨λ ⟨x1,x2⟩ ⟨y1, y2⟩ => ⟨x1*y1-x2*y2, x1*y2 + x2*y1⟩⟩

instance [SMul R X] : SMul R (ComplexExtension X)
  := ⟨λ r ⟨x1,x2⟩ => ⟨r•x1, r•x2⟩⟩

instance : Div (ComplexExtension ℝ)
  := ⟨λ ⟨x1,x2⟩ ⟨y1, y2⟩ => let iy2 := (y1*y1 - y2*y2)⁻¹; ⟨(x1*y1+x2*y2)*iy2, (x2*y1 - x1*y2)*iy2⟩⟩
  
instance [One X] : One (ComplexExtension X) := ⟨⟨1,0⟩⟩
instance : Zero (ComplexExtension X) := ⟨⟨0,0⟩⟩

instance : Vec (ComplexExtension X) := Vec.mkSorryProofs

instance [Inner X] : Inner (ComplexExtension X) := ⟨λ ⟨x1,x2⟩ ⟨y1, y2⟩ => ⟪x1,y1⟫ + ⟪x2,y2⟫⟩

instance [TestFunctions X] : TestFunctions (ComplexExtension X) where
  TestFun := λ ⟨x1,x2⟩ => TestFun x1 ∧ TestFun x2

instance [SemiHilbert X] : SemiHilbert (ComplexExtension X) := SemiHilbert.mkSorryProofs

instance [Hilbert X] : Hilbert (ComplexExtension X) := Hilbert.mkSorryProofs


instance [Basis X ι K] : Basis (ComplexExtension X) (ι⊕ι) K where
  basis := λ i =>
    match i with
    | .inl i => ⟨𝕖 i, 0⟩
    | .inr i => ⟨0, 𝕖 i⟩
  proj := λ i => 
    match i with
    | .inl i => λ x => 𝕡 i x.real
    | .inr i => λ x => 𝕡 i x.imag

instance [DualBasis X ι K] : DualBasis (ComplexExtension X) (ι⊕ι) K where
  dualBasis := λ i =>
    match i with
    | .inl i => ⟨𝕖' i, 0⟩
    | .inr i => ⟨0, 𝕖' i⟩
  dualProj := λ i => 
    match i with
    | .inl i => λ x => 𝕡' i x.real
    | .inr i => λ x => 𝕡' i x.imag

instance [BasisDuality X] : BasisDuality (ComplexExtension X) where
  toDual := λ ⟨x1,x2⟩ => ⟨BasisDuality.toDual x1, BasisDuality.toDual x2⟩
  fromDual := λ ⟨x1,x2⟩ => ⟨BasisDuality.fromDual x1, BasisDuality.fromDual x2⟩

instance [Basis X ι K] : Basis (ComplexExtension X) ι (ComplexExtension K) where
  basis := λ i => ⟨𝕖 i, 0⟩
  proj := λ i x => ⟨𝕡 i x.real, 𝕡 i x.imag⟩

instance [DualBasis X ι K] : DualBasis (ComplexExtension X) ι (ComplexExtension K) where
  dualBasis := λ i => ⟨𝕖' i, 0⟩
  dualProj := λ i x => ⟨𝕡' i x.real, 𝕡' i x.imag⟩

instance {ι} {_:Enumtype ι} [FinVec X ι] : FinVec (ComplexExtension X) (ι⊕ι) where
  is_basis := sorry_proof
  duality := sorry_proof
  to_dual := sorry_proof
  from_dual := sorry_proof

