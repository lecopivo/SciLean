-- import SciLean.Core.Objects.Vec
-- import SciLean.Core.Objects.Scalar
import SciLean.Meta.DerivingOp
import SciLean.Core
import SciLean.Core.Meta.GenerateLinearMapSimp

open SciLean


def Add.ofEquiv {X Y : Type*} [Add X] (f : X ≃ Y) : Add Y where
  add a b := f (f.symm a + f.symm b)

def Sub.ofEquiv {X Y : Type*} [Sub X] (f : X ≃ Y) : Sub Y where
  sub a b := f (f.symm a - f.symm b)

def Mul.ofEquiv {X Y : Type*} [Mul X] (f : X ≃ Y) : Mul Y where
  mul a b := f (f.symm a * f.symm b)

def Div.ofEquiv {X Y : Type*} [Div X] (f : X ≃ Y) : Div Y where
  div a b := f (f.symm a / f.symm b)

def Neg.ofEquiv {X Y : Type*} [Neg X] (f : X ≃ Y) : Neg Y where
  neg a := f (- f.symm a)

def Inv.ofEquiv {X Y : Type*} [Inv X] (f : X ≃ Y) : Inv Y where
  inv a := f (f.symm a)⁻¹

def Zero.ofEquiv {X Y : Type*} [Zero X] (f : X ≃ Y) : Zero Y where
  zero := f 0

def One.ofEquiv {X Y : Type*} [One X] (f : X ≃ Y) : One Y where
  one := f 1

def SMul.ofEquiv (R : Type*) {X Y : Type*} [SMul R X] (f : X ≃ Y) : SMul R Y where
  smul r a := f (r • f.symm a)

instance {X Y : Type*} [Add X] [Add Y] : Add ((_ : X) × Y) where
  add | ⟨x1, y1⟩, ⟨x2, y2⟩ => ⟨x1 + x2, y1 + y2⟩

instance {X Y : Type*} [Sub X] [Sub Y] : Sub ((_ : X) × Y) where
  sub | ⟨x1, y1⟩, ⟨x2, y2⟩ => ⟨x1 - x2, y1 - y2⟩

instance {X Y : Type*} [Mul X] [Mul Y] : Mul ((_ : X) × Y) where
  mul | ⟨x1, y1⟩, ⟨x2, y2⟩ => ⟨x1 * x2, y1 * y2⟩

instance {X Y : Type*} [Div X] [Div Y] : Div ((_ : X) × Y) where
  div | ⟨x1, y1⟩, ⟨x2, y2⟩ => ⟨x1 / x2, y1 / y2⟩

instance {X Y : Type*} [Neg X] [Neg Y] : Neg ((_ : X) × Y) where
  neg | ⟨x, y⟩ => ⟨-x, -y⟩

instance {X Y : Type*} [Inv X] [Inv Y] : Inv ((_ : X) × Y) where
  inv | ⟨x, y⟩ => ⟨x⁻¹, y⁻¹⟩

instance {X Y : Type*} [Zero X] [Zero Y] : Zero ((_ : X) × Y) where
  zero := ⟨0, 0⟩

instance {X Y : Type*} [One X] [One Y] : One ((_ : X) × Y) where
  one := ⟨1, 1⟩

instance {R X Y : Type*} [SMul R X] [SMul R Y] : SMul R ((_ : X) × Y) where
  smul r | ⟨x, y⟩ => ⟨r • x, r • y⟩


def TopologicalSpace.ofEquiv {X Y : Type*} [TopologicalSpace X] (f : X ≃ Y) :
    TopologicalSpace Y where
  IsOpen A := IsOpen (f⁻¹' A)
  isOpen_univ := by simp_all only [Set.preimage_univ, isOpen_univ]
  isOpen_inter := sorry_proof
  isOpen_sUnion := sorry_proof


instance {X Y : Type*} [UniformSpace X] [UniformSpace Y] : UniformSpace ((_ : X) × Y) where
  uniformity := sorry
  symm := sorry_proof
  comp := sorry_proof
  nhds_eq_comap_uniformity := sorry_proof

def UniformSpace.ofEquiv {X Y : Type*} [UniformSpace X] [TopologicalSpace Y] (f : X ≃ Y) :
    UniformSpace Y where
  uniformity := sorry
  symm := sorry_proof
  comp := sorry_proof
  nhds_eq_comap_uniformity := sorry_proof

instance {R X Y : Type*} [RCLike R] [Vec R X] [Vec R Y] : Vec R ((_ : X) × Y) := Vec.mkSorryProofs


instance {X Y} [Add R] [Inner R X] [Inner R Y] : Inner R ((_ : X) × Y) where
  inner | ⟨x1, y1⟩, ⟨x2, y2⟩ => inner x1 x2 + inner y1 y2

def Inner.ofEquiv (R : Type*) {X Y : Type*} [Inner R X] (f : X ≃ Y) : Inner R Y where
  inner a b := inner (f.symm a) (f.symm b)


instance {X Y : Type*} [TestFunctions X] [TestFunctions Y] : TestFunctions ((_ : X) × Y) where
  TestFunction | ⟨x, y⟩ => TestFunction x ∧ TestFunction y

def TestFunctions.ofEquiv {X Y : Type*} [TestFunctions X] (f : X ≃ Y) : TestFunctions Y where
  TestFunction x := TestFunction (f.symm x)

instance {R X Y : Type*} [RCLike R]
    [SemiInnerProductSpace R X] [SemiInnerProductSpace R Y] :
    SemiInnerProductSpace R ((_ : X) × Y) := SemiInnerProductSpace.mkSorryProofs

instance {X Y ι κ K} [Basis ι K X] [Basis κ K Y] [Zero X] [Zero Y] :
    Basis (ι ⊕ κ) K ((_ : X) × Y)  where
  basis := λ i =>
    match i with
    | Sum.inl ix => ⟨ⅇ ix, 0⟩
    | Sum.inr iy => ⟨0, ⅇ iy⟩
  proj := λ i x =>
    match i with
    | Sum.inl ix => ℼ ix x.1
    | Sum.inr iy => ℼ iy x.2

def Basis.ofEquiv (I K : Type*) {X Y : Type*} [Basis I K X] (f : X ≃ Y) : Basis I K Y where
  basis := λ i => f (ⅇ i)
  proj := λ i x => ℼ i (f.symm x)


instance {X Y ι κ K} [DualBasis ι K X] [DualBasis κ K Y] [Zero X] [Zero Y] :
    DualBasis (ι ⊕ κ) K ((_ : X) × Y) where
  dualBasis := λ i =>
    match i with
    | Sum.inl ix => ⟨ⅇ' ix, 0⟩
    | Sum.inr iy => ⟨0, ⅇ' iy⟩
  dualProj := λ i x =>
    match i with
    | Sum.inl ix => ℼ' ix x.1
    | Sum.inr iy => ℼ' iy x.2

def DualBasis.ofEquiv (I K : Type*) {X Y : Type*} [DualBasis I K X] (f : X ≃ Y) :
    DualBasis I K Y where
  dualBasis := λ i => f (ⅇ' i)
  dualProj := λ i x => ℼ' i (f.symm x)

open BasisDuality in
instance {X Y} [BasisDuality X] [BasisDuality Y] : BasisDuality ((_ : X) × Y) where
  toDual | ⟨x,y⟩ => ⟨toDual x, toDual y⟩
  fromDual | ⟨x,y⟩ => ⟨fromDual x, fromDual y⟩

open BasisDuality in
def BasisDuality.ofEquiv {X Y : Type*} [BasisDuality X] (f : X ≃ Y) : BasisDuality Y where
  toDual := λ x => f (toDual (f.symm x))
  fromDual := λ x => f (fromDual (f.symm x))


def StructType.ofEquiv {X I : Type*} {XI : I → Type*} {Y : Type*} [StructType X I XI]
    (f : X ≃ Y) :
    StructType Y I XI where
  structProj y i := structProj (f.symm y) i
  structMake h := f (structMake h)
  structModify i h y := f (structModify i h (f.symm y))
  left_inv := sorry_proof
  right_inv := sorry_proof
  structProj_structModify := sorry_proof
  structProj_structModify' := sorry_proof




----------------------------------------------------------------------------------------------------

structure Float3 where
  (x y z : Float)
  deriving Add, Mul, Sub, Div, Neg, Zero, One

instance : Add Float3 := (Add.ofEquiv (proxy_equiv% Float3)) rewrite_by reduce
instance : Sub Float3 := (Sub.ofEquiv (proxy_equiv% Float3)) rewrite_by reduce
instance : Neg Float3 := (Neg.ofEquiv (proxy_equiv% Float3)) rewrite_by reduce
instance : One Float3 := (One.ofEquiv (proxy_equiv% Float3)) rewrite_by reduce
instance : Zero Float3 := (Zero.ofEquiv (proxy_equiv% Float3)) rewrite_by reduce
instance : SMul Float Float3 := (SMul.ofEquiv Float (proxy_equiv% Float3)) rewrite_by reduce

instance : TopologicalSpace Float3 := TopologicalSpace.ofEquiv (proxy_equiv% _)
instance : UniformSpace Float3 := UniformSpace.ofEquiv (proxy_equiv% _)

-- this can't be done through equivalence and we need a specialized tactic
instance : Vec Float Float3 := Vec.mkSorryProofs

instance : Inner Float Float3 := Inner.ofEquiv Float (proxy_equiv% Float3) rewrite_by reduce
instance : TestFunctions Float3 := TestFunctions.ofEquiv (proxy_equiv% Float3) rewrite_by reduce

instance : SemiInnerProductSpace Float Float3 := SemiInnerProductSpace.mkSorryProofs
instance : SemiHilbert Float Float3 where test_functions_true := by simp[TestFunction]

@[instance]
def Float3.instances.StructType := StructType.ofEquiv (I:=Unit⊕Unit⊕Unit) (proxy_equiv% Float3)

instance : ZeroStruct Float3 (Unit⊕Unit⊕Unit) _ where
  structProj_zero := by intro; repeat (first | rfl | rename_i i; cases i; rfl)

instance : AddStruct Float3 (Unit⊕Unit⊕Unit) _ where
  structProj_add := by intro _ x y; repeat (first | rfl | rename_i i; cases i; rfl)

instance : SMulStruct Float Float3 (Unit⊕Unit⊕Unit) _ where
  structProj_smul := by intro _ r x; repeat (first | rfl | rename_i i; cases i; rfl)

instance : VecStruct Float Float3 (Unit⊕Unit⊕Unit) _ where
  structProj_continuous := sorry_proof
  structMake_continuous := sorry_proof



instance : SciLean.Basis (Unit⊕Unit⊕Unit) Float Float3 where
  basis := λ i => oneHot i 1
  proj := λ i x =>
    match i with
    | .inl i => structProj (I:=(Unit⊕Unit⊕Unit))  x (.inl ())
    | .inr (.inl i) => structProj (I:=Unit⊕Unit⊕Unit) x (.inr (.inl ()))
    | .inr (.inr i) => structProj (I:=Unit⊕Unit⊕Unit) x (.inr (.inr ()))



--@[as_struct_proj]
theorem Float3.x.as_struct_proj :
  Float3.x = (fun v : Float3 => (structProj (I:=Unit⊕Unit⊕Unit) v (.inl ()))) := by rfl

--@[as_struct_proj]
theorem Float3.y.as_struct_proj :
  Float3.y = (fun v : Float3 => (structProj (I:=Unit⊕Unit⊕Unit) v (.inr (.inl ())))) := by rfl

--@[as_struct_proj]
theorem Float3.z.as_struct_proj :
  Float3.z = (fun v : Float3 => (structProj (I:=Unit⊕Unit⊕Unit) v (.inr (.inr ())))) := by rfl


--@[as_struct_modify]
theorem Float3.x.as_struct_modify (f : Float → Float) (v : Float3):
  {v with x := f v.x} = (structModify (I:=Unit⊕Unit⊕Unit) (.inl ()) f v) := by rfl

--@[as_struct_modify]
theorem Float3.y.as_struct_modify (f : Float → Float) (v : Float3):
  {v with y := f v.y} = (structModify (I:=Unit⊕Unit⊕Unit) (.inr (.inl ())) f v) := by rfl

--@[as_struct_modify]
theorem Float3.z.as_struct_modify (f : Float → Float) (v : Float3):
  {v with z := f v.z} = (structModify (I:=Unit⊕Unit⊕Unit) (.inr (.inr ())) f v) := by rfl


--@[as_struct_make]
theorem Float3.mk.as_struct_make (f) :
  Float3.mk (f (.inl ())) (f (.inr (.inl ()))) (f (.inr (.inr ())))
  =
  (structMake (X:=Float3) (I:=Unit⊕Unit⊕Unit) f) := by rfl


theorem Float3.x.arg_self.IsLinearMap_rule : IsLinearMap Float (fun v => Float3.x v) := by
  rw[Float3.x.as_struct_proj]
  sorry_proof

theorem Float3.y.arg_self.IsLinearMap_rule : IsLinearMap Float (fun v => Float3.y v) := by
  rw[Float3.y.as_struct_proj]
  sorry_proof

theorem Float3.z.arg_self.IsLinearMap_rule : IsLinearMap Float (fun v => Float3.z v) := by
  rw[Float3.z.as_struct_proj]
  sorry_proof


#generate_linear_map_simps Float3.x.arg_self.IsLinearMap_rule
#generate_linear_map_simps Float3.y.arg_self.IsLinearMap_rule
#generate_linear_map_simps Float3.z.arg_self.IsLinearMap_rule



----------------------------------------------------------------------------------------------------

structure Vec2 (X : Type) where
  (x y : X)

variable (X : Type)

#check (proxy_equiv% (Vec2 X))


instance {X} [Add X] : Add (Vec2 X) := derive_add%
instance {X} [Sub X] : Sub (Vec2 X) := derive_sub%
instance {X} [Neg X] : Neg (Vec2 X) := derive_neg%
instance {X} [Zero X] : Zero (Vec2 X) := derive_zero%
instance {X} [One X]  : One (Vec2 X)  := derive_one%
instance {R} [SMul R X] : SMul R (Vec2 X) := derive_smul%

instance {R} [RCLike R] : Vec R X := Vec.mkSorryProofs

instance {R} [Inner R X] [Add X] : Inner R (Vec2 X) := derive_inner%
instance [TestFunctions X] : TestFunctions (Vec2 X) := derive_test_functions%

instance {R} [RCLike R] : SemiInnerProductSpace R Float3 := SemiInnerProductSpace.mkSorryProofs
instance {R} [RCLike R] : SemiHilbert R Float3 := SemiHilbert.mkSorryProofs


-- Non-nested StructType
inductive Vec2.FieldIndex where
  | x | y

abbrev Vec2.FieldType (X : Type) (i : Vec2.FieldIndex) := X

-- if all fields have the same type do not use `Vec2.Type`
instance : StructType (Vec2 X) (Vec2.FieldIndex I) (fun _ => X) := derive_structtype%



-- Nested StructType -- probably ignore for the time being
inductive Vec2.Index (Ix Iy : Type) where
  | x (i : Ix) | y (i : Iy)

abbrev Vec2.FieldType (XI : Ix → Type) (YI : Iy → Type) (i : Vec2.Index Ix Iy) :=
  match i with
  | .x i => XI i
  | .y i => YI i

instance [StructType X I XI] : StructType (Vec2 X) (Vec2.Index I)
----------------------------------------------------------------------------------------------------

structure Ball (R X : Type) where
  center : R
  radius : X
  deriving Add, SMul R


Add R → Add X → Add (Ball R X)
Mul R → SMul R X → SMul (Ball R X)
