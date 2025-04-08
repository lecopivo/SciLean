import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.TangentSpace
import SciLean.Analysis.Diffeology.VecDiffeology
import SciLean.Analysis.Diffeology.Option
import SciLean.Analysis.Calculus.ContDiff
import SciLean.Util.RewriteBy

namespace SciLean

local notation:max "ℝ^" n:max => Fin n → ℝ


@[ext]
structure ArrayTangentSpace
    {X : Type u} [Diffeology X] {TX : outParam (X → Type v)}
    [(x : X) → AddCommGroup (TX x)] [(x : X) → outParam (Module ℝ (TX x))] [ts: TangentSpace X TX]
    (x : Array X) where
  data : Array (Σ T : Type v, T)
  data_size : data.size = x.size
  data_cast : ∀ i : Fin x.size, data[i].1 = TX (x[i])


variable
  {X : Type u} [Diffeology X] {TX : outParam (X → Type v)}
  [(x : X) → AddCommGroup (TX x)] [(x : X) → outParam (Module ℝ (TX x))] [ts: TangentSpace X TX]


namespace ArrayTangentSpace


def get {x : Array X} (dx : ArrayTangentSpace x) (i : Fin x.size) : TX x[i] :=
  let i' : Fin dx.data.size := ⟨i, by have := dx.data_size; omega⟩
  cast (dx.data_cast i) (dx.data[i']).2


theorem ext_get {x : Array X} (dx dx' : ArrayTangentSpace x) :
    (∀ i, dx.get i = dx'.get i) → dx = dx' := by
  intro h
  ext
  · rw[dx.data_size]; rw[dx'.data_size]
  · simp[ArrayTangentSpace.get] at h
    sorry
  · sorry


def castBase {x : Array X} (dx : ArrayTangentSpace x) (y : Array X) (h : x = y) : ArrayTangentSpace y :=
  by subst h; exact dx


@[simp]
theorem castBase_get {x y : Array X} (h : x = y) (dx : ArrayTangentSpace x) (i : Fin y.size) :
  (dx.castBase y h).get i = cast (by simp[h]) (dx.get ⟨i, h ▸ i.2⟩) := by
  subst h
  simp[castBase,ArrayTangentSpace.get]


def ofFn {x : Array X} (f : (i : Fin x.size) → TX x[i]) : ArrayTangentSpace x where
  data := .ofFn (fun i => ⟨TX x[i], f i⟩)
  data_size := by simp
  data_cast := by intro i; simp


@[simp]
theorem get_ofFn {x : Array X} (f : (i : Fin x.size) → TX x[i]) (i : Fin x.size) :
  (ofFn f).get i = f i := by
  simp[ofFn, get]
  sorry


def ofFnCast {x : Array X} {TX' : Fin s → Type _} (f : (i : Fin s) → TX' i)
    (hn : x.size = s) (h : ∀ i : Fin s, TX' i = TX x[i]) : ArrayTangentSpace x where
  data := .ofFn (fun i => ⟨TX x[i], cast (by simp_all) (f i)⟩)
  data_size := by simp_all
  data_cast := by intro i; simp


@[simp]
theorem get_ofFnCast {x : Array X} {TX' : Fin s → Type _} (f : (i : Fin s) → TX' i)
    (hn : x.size = s) (h : ∀ i : Fin s, TX' i = TX x[i]) :
  (ofFnCast f hn h).get = cast (by subst hn; sorry) f := by
  subst hn
  simp[ofFnCast, get]
  sorry


def mapIdx {x : Array X} (dx  : ArrayTangentSpace x)
           (f : (i : Fin x.size) → TX x[i] → TX x[i]) : ArrayTangentSpace x :=
  .ofFn (fun i => f i (dx.get i))


@[simp]
theorem get_mapIdx {x : Array X} (dx : ArrayTangentSpace x)
      (f : (i : Fin x.size) → TX x[i] → TX x[i]) (i : Fin x.size) :
  (dx.mapIdx f).get i = f i (dx.get i) := by
  simp[mapIdx]


def append {x y : Array X} (dx : ArrayTangentSpace x) (dy : ArrayTangentSpace y) :
    ArrayTangentSpace (x ++ y) where
  data := dx.data ++ dy.data
  data_size := by simp[dx.data_size, dy.data_size]
  data_cast := by
    intro i
    have : dx.data.size = x.size := by rw[dx.data_size]
    by_cases h : i.val < x.size
    · have h' : i.val < dx.data.size := by rw[dx.data_size]; exact h
      simp[Array.getElem_append,h,h']
      exact dx.data_cast ⟨i.val, h⟩
    · have h' : ¬(i < dx.data.size) := by rw[dx.data_size]; omega
      simp[Array.getElem_append,h,h']
      have := dy.data_cast ⟨i.val - dx.data.size, by simp_all; have :=i.2; simp_all; omega⟩
      simp_all


theorem get_append {x y : Array X} (dx : ArrayTangentSpace x) (dy : ArrayTangentSpace y) (i : Fin (x ++ y).size) :
  (dx.append dy).get i
  =
  if h : i < x.size then
    cast (by simp[Array.getElem_append,h]) (dx.get ⟨i, by have :=i.2; simp_all⟩)
  else
    cast (by simp[Array.getElem_append,h]) (dy.get ⟨i-x.size, by have :=i.2; simp_all; omega⟩) := sorry


def set {x : Array X} (dx : ArrayTangentSpace x) (i : Fin x.size) (dxi : TX x[i]) : ArrayTangentSpace x where
  data := dx.data.set ⟨i,by simp[dx.data_size]⟩ ⟨_,dxi⟩
  data_size := by simp[dx.data_size]
  data_cast := by
    simp[Array.getElem_set]
    intro j
    split_ifs with h
    · cases i; cases j; simp at h; substs h; rfl
    · have h' := (dx.data_cast j) rewrite_type_by simp
      exact h'


----------------------------------------------------------------------------------------------------
-- Operations --------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance {x : Array X} : Add (ArrayTangentSpace x) :=
  ⟨fun dx dy => dx.mapIdx (fun i xi => xi + dy.get i)⟩

@[simp]
theorem add_get {x : Array X} (dx dy : ArrayTangentSpace x) (i : Fin x.size) :
  (dx + dy).get i = dx.get i + dy.get i := by
  simp[HAdd.hAdd,Add.add]

instance {x : Array X} : Sub (ArrayTangentSpace x) :=
  ⟨fun dx dy => dx.mapIdx (fun i xi => xi - dy.get i)⟩

@[simp]
theorem sub_get {x : Array X} (dx dy : ArrayTangentSpace x) (i : Fin x.size) :
  (dx - dy).get i = dx.get i - dy.get i := by
  simp[HSub.hSub,Sub.sub]

instance {x : Array X} : Neg (ArrayTangentSpace x) :=
  ⟨fun dx => dx.mapIdx (fun _ xi => -xi)⟩

@[simp]
theorem neg_get {x : Array X} (dx : ArrayTangentSpace x) (i : Fin x.size) :
  (-dx).get i = -dx.get i := by
  simp[Neg.neg]

instance {x : Array X} : SMul ℝ (ArrayTangentSpace x) :=
  ⟨fun r dx => dx.mapIdx (fun _ xi => r • xi)⟩

@[simp]
theorem smul_get {x : Array X} (r : ℝ) (dx : ArrayTangentSpace x) (i : Fin x.size) :
  (r • dx).get i = r • dx.get i := by
  simp[HSMul.hSMul,SMul.smul]

instance {x : Array X} : Zero (ArrayTangentSpace x) :=
  ⟨ofFn (fun _ => 0)⟩

@[simp]
theorem zero_get {x : Array X} (i : Fin x.size) :
  (0 : ArrayTangentSpace x).get i = 0 := by
  simp[Zero.zero,OfNat.ofNat]


----------------------------------------------------------------------------------------------------
-- Algebra -----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance {x : Array X} : AddCommGroup (ArrayTangentSpace x) :=
  { add_assoc := by
      intro a b c
      apply ext_get
      intro i
      simp
      rw[add_assoc]
    , zero_add := by
      intro a
      apply ext_get
      intro i
      simp
    , add_zero := by
      intro a
      apply ext_get
      intro i
      simp
    , add_comm := by
      intro a b
      apply ext_get
      intro i
      simp
      rw[add_comm]
    , nsmul := fun n dx => dx.mapIdx (fun _ xi => (n:ℝ) • xi)
    , nsmul_zero := by
      intro n
      apply ext_get
      intro i
      simp
    , nsmul_succ := by
      intro n dx
      apply ext_get
      intro i
      simp; module
    , zsmul := fun z dx => dx.mapIdx (fun _ xi => (z:ℝ) • xi)
    , zsmul_zero' := by
      intro dx
      apply ext_get
      intro i
      simp
    , zsmul_succ' := by
      intro n dx
      apply ext_get
      intro i
      simp; module
    , zsmul_neg' := by
      intro n dx
      apply ext_get
      intro i
      simp; module
    , neg_add_cancel := by
      intro a
      apply ext_get
      intro i
      simp
    , sub_eq_add_neg := by
      intro a b
      apply ext_get
      intro i
      simp[sub_eq_add_neg]
    }


instance {x : Array X} : Module ℝ (ArrayTangentSpace x) where
  smul_add := by
    intro r dx dy
    apply ext_get
    intro i
    simp
  smul_zero := by
    intro r
    apply ext_get
    intro i
    simp
  one_smul := by
    intro dx
    apply ext_get
    intro i
    simp
  mul_smul := by
    intro r s dx
    apply ext_get
    intro i
    simp[mul_smul]
  add_smul := by
    intro r s dx
    apply ext_get
    intro i
    simp[add_smul]
  zero_smul := by
    intro dx
    apply ext_get
    intro i
    simp
