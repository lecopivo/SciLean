import SciLean

open SciLean

-- This look like a good idea to have such that we do not have to deal with XI in some cases
section MoveMe
  class UniformStructType (X : Sort _) (R : Sort _) (I : outParam (Sort _)) {XI : outParam <| I → Sort _}
      [StructType X I XI] : Prop where
    uniform_return_type : ∀ i, XI i = R

  open UniformStructType in
  abbrev uniformStructProj (R : Sort _) {X : Sort _}  {I : Sort _} {XI : I → Sort _}
      [StructType X I XI] [UniformStructType X R I] (x : X) (i : I) : R :=
    uniform_return_type (R:=R) X i ▸ structProj (I:=I) x i
end MoveMe


-- instance {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] : AddCommGroup ((_ : X) × Y) where
--   add_assoc := sorry_proof
--   zero_add := sorry_proof
--   add_zero := sorry_proof
--   nsmul n := fun ⟨x,y⟩ => ⟨n•x, n•y⟩
--   zsmul i := fun ⟨x,y⟩ => ⟨i•x, i•y⟩
--   neg_add_cancel := sorry_proof
--   add_comm := sorry_proof

#exit
instance {R X Y : Type*} [RCLike R] [Vec R X] [Vec R Y] : Vec R ((_ : X) × Y) := Vec.mkSorryProofs

instance {X Y : Type*} [TestFunctions X] [TestFunctions Y] : TestFunctions ((_ : X) × Y) where
  TestFunction | ⟨x, y⟩ => TestFunction x ∧ TestFunction y

def TestFunctions.ofEquiv {X Y : Type*} [TestFunctions X] (f : X ≃ Y) : TestFunctions Y where
  TestFunction x := TestFunction (f.symm x)

instance {R X Y : Type*} [RCLike R]
    [SemiInnerProductSpace R X] [SemiInnerProductSpace R Y] :
    SemiInnerProductSpace R ((_ : X) × Y) := SemiInnerProductSpace.mkSorryProofs

instance {X Y ι κ K} [Basis ι K X] [Basis κ K Y] [Zero X] [Zero Y] :
    Basis (ι ⊕ κ) K ((_ : X) × Y) where
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



#exit

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

-- Right now we have to provide `I` explicitely, can we automate this?
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

instance Float3.instances.UniformStructIndex : UniformStructType Float3 Float (Unit⊕Unit⊕Unit) where
  uniform_return_type := by intro _; repeat (first | rfl | rename_i i; cases i; rfl)

instance : SciLean.Basis (Unit⊕Unit⊕Unit) Float Float3 where
  basis := λ i => oneHot i 1
  proj := λ i x => uniformStructProj Float x i

instance : SciLean.DualBasis (Unit⊕Unit⊕Unit) Float Float3 where
  dualBasis := λ i => oneHot i 1
  dualProj := λ i x => uniformStructProj Float x i

instance : OrthonormalBasis (Unit⊕Unit⊕Unit) Float Float3 where
  is_orthogonal := sorry_proof
  is_orthonormal := sorry_proof


-- StructType theorems for `Float.x` -----------------------------------------
--@[as_struct_proj]
theorem Float3.x.as_struct_proj :
  Float3.x = (fun v : Float3 => (structProj (I:=Unit⊕Unit⊕Unit) v (.inl ()))) := by rfl

--@[as_struct_modify]
theorem Float3.x.as_struct_modify (f : Float → Float) (v : Float3):
  {v with x := f v.x} = (structModify (I:=Unit⊕Unit⊕Unit) (.inl ()) f v) := by rfl


-- StructType theorems for `Float.y` -----------------------------------------

--@[as_struct_proj]
theorem Float3.y.as_struct_proj :
  Float3.y = (fun v : Float3 => (structProj (I:=Unit⊕Unit⊕Unit) v (.inr (.inl ())))) := by rfl

--@[as_struct_modify]
theorem Float3.y.as_struct_modify (f : Float → Float) (v : Float3):
  {v with y := f v.y} = (structModify (I:=Unit⊕Unit⊕Unit) (.inr (.inl ())) f v) := by rfl


-- StructType theorems for `Float.z` -----------------------------------------

--@[as_struct_proj]
theorem Float3.z.as_struct_proj :
  Float3.z = (fun v : Float3 => (structProj (I:=Unit⊕Unit⊕Unit) v (.inr (.inr ())))) := by rfl

--@[as_struct_modify]
theorem Float3.z.as_struct_modify (f : Float → Float) (v : Float3):
  {v with z := f v.z} = (structModify (I:=Unit⊕Unit⊕Unit) (.inr (.inr ())) f v) := by rfl

-- StructType thorems for `Float.mk` -----------------------------------------

--@[as_struct_make]
theorem Float3.mk.as_struct_make (f) :
  Float3.mk (f (.inl ())) (f (.inr (.inl ()))) (f (.inr (.inr ())))
  =
  (structMake (X:=Float3) (I:=Unit⊕Unit⊕Unit) f) := by rfl


-- Float3.x properties ---------------------------------------------------
@[fun_prop]
theorem Float3.x.arg_self.IsLinearMap_rule : IsLinearMap Float (fun v => Float3.x v) := by
  rw[Float3.x.as_struct_proj]
  sorry_proof -- use fact about structProj

#generate_linear_map_simps Float3.x.arg_self.IsLinearMap_rule


-- todo add transformation rules

-- Float3.y properties ---------------------------------------------------
-- ditto

-- Float3.z properties ---------------------------------------------------
-- ditto




variable (v : Float3)
#check fun i => uniformStructProj Float v i

----------------------------------------------------------------------------------------------------

#exit
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
