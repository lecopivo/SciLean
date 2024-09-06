import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.ProxyType

import SciLean.Analysis.AdjointSpace.Basic

import SciLean.Util.SorryProof
import SciLean.Util.RewriteBy



----------------------------------------------------------------------------------------------------
-- Operations --------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

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

instance {X Y : Type*} [Norm X] [Norm Y] : Norm ((_ : X) × Y) where
  norm := fun ⟨a,b⟩ => ‖a‖ ⊔ ‖b‖

instance {R X Y : Type*} [Add R] [Inner R X] [Inner R Y] : Inner R ((_ : X) × Y) where
  inner := fun ⟨a,b⟩ ⟨c,d⟩ => ⟪a,c⟫_R + ⟪b,d⟫_R


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

def Norm.ofEquiv {X Y : Type*} [Norm X] (f : X ≃ Y) : Norm Y where
  norm := fun y => ‖f.symm y‖

def Inner.ofEquiv {R X Y : Type*} [Inner R X] (f : X ≃ Y) : Inner R Y where
  inner := fun y y' => ⟪f.symm y, f.symm y'⟫_R


----------------------------------------------------------------------------------------------------
-- Algebra -----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- todo: split this into more class instances
instance {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] : AddCommGroup ((_ : X) × Y) where
  add_assoc := sorry_proof
  zero_add := sorry_proof
  add_zero := sorry_proof
  sub := fun ⟨a,b⟩ ⟨c,d⟩ => ⟨a-c,b-d⟩
  sub_eq_add_neg := sorry_proof
  nsmul := fun n ⟨x,y⟩ => ⟨n•x, n•y⟩
  nsmul_zero := sorry_proof
  nsmul_succ := sorry_proof
  zsmul := fun i ⟨x,y⟩ => ⟨i•x, i•y⟩
  zsmul_zero' := sorry_proof
  zsmul_succ' := sorry_proof
  zsmul_neg' := sorry_proof
  neg_add_cancel := sorry_proof
  add_comm := sorry_proof

-- todo: split this into more class instances
instance {R X Y : Type*} [Semiring R] [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y] :
    Module R ((_ : X) × Y) where
  one_smul := sorry_proof
  mul_smul := sorry_proof
  smul_zero := sorry_proof
  smul_add := sorry_proof
  add_smul := sorry_proof
  zero_smul := sorry_proof

def AddCommGroup.ofEquiv {X Y : Type*} [AddCommGroup X] (f : X ≃ Y) : AddCommGroup Y where
  add := fun y y' => f (f.symm y + f.symm y')
  zero := f 0
  neg := fun y => f (- f.symm y)
  add_assoc := sorry_proof
  zero_add := sorry_proof
  add_zero := sorry_proof
  sub := fun y y' => f (f.symm y - f.symm y')
  sub_eq_add_neg := sorry_proof
  nsmul := fun n y => f (n•f.symm y)
  nsmul_zero := sorry_proof
  nsmul_succ := sorry_proof
  zsmul := fun i y => f (i•f.symm y)
  zsmul_zero' := sorry_proof
  zsmul_succ' := sorry_proof
  zsmul_neg' := sorry_proof
  neg_add_cancel := sorry_proof
  add_comm := sorry_proof

def Module.ofEquiv  {R X Y : Type*} [Semiring R] [AddCommGroup X] [Module R X] [AddCommGroup Y]
    (f : X ≃ Y) : Module R Y where
  smul := fun r y => f (r•f.symm y)
  one_smul := sorry_proof
  mul_smul := sorry_proof
  smul_zero := sorry_proof
  smul_add := sorry_proof
  add_smul := sorry_proof
  zero_smul := sorry_proof


----------------------------------------------------------------------------------------------------
-- Topology ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance {X Y : Type*} [UniformSpace X] [UniformSpace Y] : UniformSpace ((_ : X) × Y) where
  uniformity := default -- TODO: fix this!!!
  symm := sorry_proof
  comp := sorry_proof
  nhds_eq_comap_uniformity := sorry_proof

instance {X Y : Type*} [MetricSpace X] [MetricSpace Y] : MetricSpace ((_ : X) × Y) where
  dist := fun ⟨a,b⟩ ⟨c,d⟩ => (dist a c) ⊔ (dist b d)
  dist_self := sorry_proof
  dist_comm := sorry_proof
  dist_triangle := sorry_proof
  eq_of_dist_eq_zero := sorry_proof

def TopologicalSpace.ofEquiv {X Y : Type*} [TopologicalSpace X] (f : X ≃ Y) :
    TopologicalSpace Y where
  IsOpen A := IsOpen (f⁻¹' A)
  isOpen_univ := by simp_all only [Set.preimage_univ, isOpen_univ]
  isOpen_inter := sorry_proof
  isOpen_sUnion := sorry_proof

def UniformSpace.ofEquiv {X Y : Type*} [UniformSpace X] [TopologicalSpace Y] (f : X ≃ Y) :
    UniformSpace Y where
  uniformity := default -- TODO: fix this !!!!
  symm := sorry_proof
  comp := sorry_proof
  nhds_eq_comap_uniformity := sorry_proof

def UniformSpace.ofEquiv' {X Y : Type*} [UniformSpace X] (f : X ≃ Y) :
    UniformSpace Y := by
  have : TopologicalSpace Y := TopologicalSpace.ofEquiv f
  apply UniformSpace.ofEquiv f

def MetricSpace.ofEquiv {X Y : Type*} [MetricSpace X] (f : X ≃ Y) :
    MetricSpace Y where
  dist := fun y y' => (dist (f.symm y) (f.symm y'))
  dist_self := sorry_proof
  dist_comm := sorry_proof
  dist_triangle := sorry_proof
  eq_of_dist_eq_zero := sorry_proof


----------------------------------------------------------------------------------------------------
-- Analysis ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


instance {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] :
    NormedAddCommGroup ((_ : X) × Y) where
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := sorry_proof

instance {R X Y : Type*} [RCLike R]
    [NormedAddCommGroup X] [NormedSpace R X]
    [NormedAddCommGroup Y] [NormedSpace R Y] :
    NormedSpace R ((_ : X) × Y) where
  norm_smul_le := sorry_proof

instance {R X Y : Type*} [RCLike R]
    [NormedAddCommGroup X] [AdjointSpace R X]
    [NormedAddCommGroup Y] [AdjointSpace R Y] :
    AdjointSpace R ((_ : X) × Y) where
  inner_top_equiv_norm := sorry_proof
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof


def NormedAddCommGroup.ofEquiv {X Y : Type*} [NormedAddCommGroup X]
    [Norm Y] [AddCommGroup Y] [MetricSpace Y] (f : X ≃ Y) : NormedAddCommGroup Y where
  dist_eq := sorry_proof

def NormedAddCommGroup.ofEquiv' {X Y : Type*} [NormedAddCommGroup X] (f : X ≃ Y) : NormedAddCommGroup Y := by
  have : Norm Y := Norm.ofEquiv f
  have : AddCommGroup Y := AddCommGroup.ofEquiv f
  have : MetricSpace Y := MetricSpace.ofEquiv f
  apply NormedAddCommGroup.ofEquiv f

def NormedSpace.ofEquiv {R X Y : Type*} [RCLike R] [NormedAddCommGroup X] [NormedSpace R X]
    [NormedAddCommGroup Y] [Module R Y] (f : X ≃ Y) : NormedSpace R Y where
  norm_smul_le := sorry_proof

def NormedSpace.ofEquiv' {R X Y : Type*} [RCLike R] [NormedAddCommGroup X] [NormedSpace R X]
    [NormedAddCommGroup Y] (f : X ≃ Y) : NormedSpace R Y := by
  have : Module R Y := Module.ofEquiv f
  apply NormedSpace.ofEquiv f

def AdjointSpace.ofEquiv {R X Y : Type*} [RCLike R] [NormedAddCommGroup X] [AdjointSpace R X]
    [NormedAddCommGroup Y] [Inner R Y] [NormedSpace R Y] (f : X ≃ Y) : AdjointSpace R Y where
  inner_top_equiv_norm := sorry_proof
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof

def AdjointSpace.ofEquiv' {R X Y : Type*} [RCLike R] [NormedAddCommGroup X] [AdjointSpace R X]
    [NormedAddCommGroup Y] (f : X ≃ Y) : AdjointSpace R Y := by
  have : NormedSpace R Y := NormedSpace.ofEquiv' f
  have : Inner R Y := Inner.ofEquiv f
  apply AdjointSpace.ofEquiv f


structure Vec3 (R : Type*) where
  (x y z : R)

instance {R : Type*} [NormedAddCommGroup R] : NormedAddCommGroup (Vec3 R) :=
  (NormedAddCommGroup.ofEquiv' (proxy_equiv% (Vec3 R)))

instance {R X : Type*} [RCLike R] [NormedAddCommGroup X] [AdjointSpace R X] :
    AdjointSpace R (Vec3 X) := (AdjointSpace.ofEquiv' (proxy_equiv% (Vec3 X)))


-- #synth NormedSpace ℝ (Vec3 ℝ)

-- deriving_instance (X) [NormeAddCommGroup X] : NormedAddCommGroup (Vec3 X)
-- deriving_instance (R) [RCLike R] : NormedSpace R (Vec3 R)
