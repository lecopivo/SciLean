import SciLean.Core.Objects.FinVec

import Mathlib.Tactic.FunTrans.Attr
import Mathlib.Tactic.FunTrans.Elab

namespace SciLean

#exit -- very old file that needs to be completely redone

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

instance [HDiv X R X] : HDiv (ComplexExtension X) R (ComplexExtension X)
  := ⟨λ ⟨x1,x2⟩ r => ⟨x1/r, x2/r⟩⟩

instance : Inv (ComplexExtension ℝ)
  := ⟨λ ⟨x1,x2⟩ => let ix2 := (x1*x1 + x2*x2)⁻¹; ⟨ix2*x1, -ix2*x2⟩⟩

instance : Div (ComplexExtension ℝ)
  := ⟨λ ⟨x1,x2⟩ ⟨y1, y2⟩ => let iy2 := (y1*y1 + y2*y2)⁻¹; ⟨(x1*y1+x2*y2)*iy2, (x2*y1 - x1*y2)*iy2⟩⟩

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

instance {ι} {_:EnumType ι} [FinVec X ι] : FinVec (ComplexExtension X) (ι⊕ι) where
  is_basis := sorry_proof
  duality := sorry_proof
  to_dual := sorry_proof
  from_dual := sorry_proof

instance [ToString X] : ToString (ComplexExtension X) := ⟨λ ⟨x,y⟩ => s!"{x} + i*{y}"⟩

def Complex.exp (z : ℂ) : ℂ := (z.real.exp) • ⟨Real.cos z.imag, Real.sin z.imag⟩

def Complex.cos (z : ℂ) : ℂ :=
  let cx := Real.cos z.real
  let sx := Real.sin z.real
  let ey := Real.exp z.imag
  let iey2 := ey^(-2)
  (ey * (2:ℝ)⁻¹) • ⟨cx * (1 + iey2), - sx * (1 - iey2)⟩

def Complex.sin (z : ℂ) : ℂ :=
  let cx := Real.cos z.real
  let sx := Real.sin z.real
  let ey := Real.exp z.imag
  let iey2 := ey^(-2)
  (ey * (2:ℝ)⁻¹) • ⟨sx * (1 + iey2), cx * (1 - iey2)⟩

def Complex.cos' (z : ℂ) : ℂ := (2:ℝ)⁻¹ • (Complex.exp (⟨0,1⟩*z) + Complex.exp (-⟨0,1⟩*z))
def Complex.sin' (z : ℂ) : ℂ := ((2:ℝ)•(⟨0,1⟩:ℂ))⁻¹ * (Complex.exp (⟨0,1⟩*z) - Complex.exp (-⟨0,1⟩*z))

@[simp]
theorem smul_complex_mk [SMul R X] (x y : X) (r : R)
  : r • (⟨x,y⟩ : ComplexExtension X)
    =
    ⟨r•x, r•y⟩
  := by rfl

@[simp]
theorem mul_complex_mk [Add X] [Sub X] [Mul X] (x y a b : X)
  : (⟨x,y⟩ : ComplexExtension X) * ⟨a,b⟩
    =
    ⟨x*a - y*b, x*b + y*a⟩
  := by rfl

@[simp]
theorem neg_complex_mk [Neg X] (x y : X)
  : - (⟨x,y⟩ : ComplexExtension X)
    =
    ⟨-x, -y⟩
  := by rfl

@[simp]
theorem Real.exp.arg_x.complexify_simp
  : complexify Real.exp
    =
    Complex.exp
  := sorry

@[simp]
theorem Real.sin.arg_x.complexify_simp
  : complexify Real.sin
    =
    Complex.sin
  := sorry

@[simp]
theorem Real.cos.arg_x.complexify_simp
  : complexify Real.cos
    =
    Complex.cos
  := sorry

instance Inner.inner.arg_x.IsAnalytic {X} [Hilbert X] (y : X)
  : IsAnalytic (λ x : X => ⟪x, y⟫) := sorry

@[simp]
theorem Inner.inner.arg_x.complexify_simp {X} [Hilbert X] (y : X)
  : complexify (λ x => ⟪x, y⟫)
    =
    λ x => ⟨ ⟪x.real,y⟫, ⟪x.imag,y⟫ ⟩
  := sorry

instance Inner.inner.arg_y.IsAnalytic {X} [Hilbert X] (x : X)
  : IsAnalytic (λ y : X => ⟪x, y⟫) := sorry

@[simp]
theorem Inner.inner.arg_y.complexify_simp {X} [Hilbert X] (x : X)
  : complexify (λ y => ⟪x, y⟫)
    =
    λ y => ⟨ ⟪x,y.real⟫, ⟪x,y.imag⟫ ⟩
  := sorry

instance Inner.inner.arg_xy.IsAnalytic {X} [Hilbert X]
  : IsAnalytic (λ xy : X×X => ⟪xy.1, xy.2⟫) := sorry

@[simp]
theorem Inner.inner.arg_xy.complexify_simp {X} [Hilbert X]
  : complexify (λ xy : X × X => ⟪xy.1, xy.2⟫)
    =
    λ xy =>
      ⟨ ⟪xy.real.1, xy.real.2⟫ - ⟪xy.imag.1, xy.imag.2⟫, ⟪xy.real.1, xy.imag.2⟫ + ⟪xy.imag.1, xy.real.2⟫ ⟩
  := sorry

instance Inner.inner.arg_xy.IsAnalytic' {X} [Hilbert X] {T} [Vec T] (x y : T → X) [SciLean.IsAnalytic x] [SciLean.IsAnalytic y]
  : SciLean.IsAnalytic (λ t => ⟪x t, y t⟫) := sorry

@[simp]
theorem Inner.inner.arg_xy.complexify_simp' {X} [Hilbert X] {T} [Vec T] (x y : T → X)
  : complexify (λ t => ⟪x t, y t⟫)
    =
    λ t =>
      let x' := complexify x t
      let y' := complexify y t
      ⟨ ⟪x'.real, y'.real⟫ - ⟪x'.imag, y'.imag⟫, ⟪x'.real, y'.imag⟫ + ⟪x'.imag, y'.real⟫ ⟩
  := sorry
