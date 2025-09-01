import SciLean.Data.FinProd
import SciLean.Data.ListN
import SciLean.Data.DataArray
import Mathlib.Tactic.Ring
import SciLean.Tactic.CompiledTactics

namespace SciLean

/-- Dimensions of rank `r` tensor `#[d₁,...,dᵣ]'`.

Each dimension has indices in the range `0,...,dᵢ-1` -/
abbrev Dims (rank : ℕ) := Vector ℤ rank

/-- Dimensions of rank `r` tensor `#[(a₁,b₁),...,(aᵣ,bᵣ)]'`.

Each dimension has indices in the range `-aᵢ,...,bᵢ` -/
abbrev DimsI (rank : ℕ) := Vector (ℤ×ℤ) rank

/-- Padding of rank `r` tensor `#[(l₁,h₁),...,(lᵣ,hᵣ)]'`

Tensors dimensions are padded to yiled
  - `-lᵢ,...,dᵢ+hᵢ-1`
  - `aᵢ-lᵢ,...,bᵢ+hᵢ` -/
abbrev Padding (rank : ℕ) := Vector (ℤ×ℤ) rank


/-- Tensor index of rank `r` tensor with dimensions `dims := #[d₁,...,dᵣ]'`. -/
@[ext]
structure TensorIndex {r} (dims : Dims r) where
  val : Vector ℤ r
  bounds : ∀ (i : Fin r), 0 ≤ val[i] ∧ val[i] < dims[i]


/-- Tensor index of rank `r` tensor with dimensions `dims := #[(a₁,b₁),...,(aᵣ,bᵣ)]'`. -/
@[ext]
structure TensorIndexI {r} (dims : DimsI r) where
  val : Vector ℤ r
  bounds : ∀ (i : Fin r), dims[i].1 ≤ val[i] ∧ val[i] ≤ dims[i].2

instance {r} {dim : Dims r} : GetElem (TensorIndex dim) (Fin r) ℤ (fun _ _ => True) where
  getElem x i _ := x.val[i]

instance {r} {dim : DimsI r} : GetElem (TensorIndexI dim) (Fin r) ℤ (fun _ _ => True) where
  getElem x i _ := x.val[i]

instance {r} {dim : Dims r} : DecidableEq (TensorIndex dim) :=
  fun x y =>
    if h : x.val = y.val then
      .isTrue (by cases x; simp_all)
    else
      .isFalse (by by_contra h; simp_all)

instance {r} {dim : DimsI r} : DecidableEq (TensorIndexI dim) :=
  fun x y =>
    if h : x.val = y.val then
      .isTrue (by cases x; simp_all)
    else
      .isFalse (by by_contra h; simp_all)

@[simp]
theorem TensorIndex.get_le {r} {dim : Dims r} (i : TensorIndex dim) :
    ∀ (d : Fin r), 0 ≤ i[d] ∧ i[d] < dim[d] := i.2

def TensorIndex.bounds' {r} {dims : Dims r} (i : TensorIndex dims) :
    ∀ d, (0:ℤ) ≤ i[d] ∧ i[d] < dims[d] := by
  intro d; have := i.2 d; simp_all only [get_le, and_self]

@[simp]
theorem TensorIndexI.get_le {r} {dim : DimsI r} (i : TensorIndexI dim) :
    ∀ (d : Fin r), dim[d].1 ≤ i[d] ∧ i[d] ≤ dim[d].2 := i.2


instance {r} {dims : Dims r}  : IndexType (TensorIndex  dims) := sorry
instance {r} {dims : DimsI r} : IndexType (TensorIndexI dims) := sorry

def convDim {r} (spDims kerDim : Dims r) (pad : Padding r) : Dims r :=
  .ofFn fun i =>
    let n : Int := spDims[i]
    let m : Int := kerDim[i]
    let lh := pad[i]
    n - m + lh.1 + lh.2

def convDimI {r} (spDims kerDim : DimsI r) (pad : Padding r) : DimsI r :=
  .ofFn fun i =>
    let ab := spDims[i]
    let cd := kerDim[i]
    let lh := pad[i]
    (ab.1 - lh.1 - cd.1, ab.2 + lh.2 - cd.2)


/-- Padding for reverse pass given kernel dimensions -/
def Padding.rev (kerDim : Dims r) (pad : Padding r) : Padding r :=
  .ofFn fun i => (kerDim[i] - pad[i].1, kerDim[i] - pad[i].2)

/-- Padding for reverse pass given kernel dimensions -/
def Padding.revI (pad : Padding r) (kerDim : DimsI r) : Padding r :=
  .ofFn fun i =>
    let m := kerDim[i].2 - kerDim[i].1
    (m - pad[i].1, m - pad[i].2)

def DimsI.rev (kerDim : DimsI r) : DimsI r :=
  .ofFn fun i => (-kerDim[i].2, -kerDim[i].1)

@[simp]
theorem DimsI.rev_rev (dims : DimsI r) : dims.rev.rev = dims := by ext <;> simp_all[DimsI.rev]

def TensorIndexI.rev {dims : DimsI r} (i : TensorIndexI dims)
    {outDims} (houtDims : outDims = dims.rev := by (try simp_all); (try infer_var)) :
    TensorIndexI outDims :=
{
  val := .ofFn fun d => -i[d]
  bounds := by simp_all[DimsI.rev]
}


def DimsI.pad (spDim : DimsI r) (pad : Padding r) : DimsI r :=
  .ofFn fun i => (spDim[i].1 - pad[i].1, spDim[i].2 + pad[i].2)


def Dims.pad (spDim : Dims r) (pad : Padding r) : DimsI r :=
  .ofFn fun i => (0- pad[i].1, spDim[i] + pad[i].2)


@[simp]
theorem convDim_swap {r} (spDims kerDim : Dims r) (pad : Padding r) :
    convDim spDims (convDim spDims kerDim pad) pad
    =
    kerDim := by
  ext; simp[convDim]; ring

@[simp]
theorem convDim_swap' {r} (spDims kerDim : Dims r) (pad : Padding r) :
    convDim (convDim spDims kerDim pad) kerDim (pad.rev kerDim)
    =
    spDims := by
  ext; simp[convDim,Padding.rev]; ring

@[simp]
theorem convDimI_swap {r} (spDims kerDim : DimsI r) (pad : Padding r) :
    convDimI spDims (convDimI spDims kerDim pad) pad
    =
    kerDim := by
  ext <;> simp[convDimI]

@[simp]
theorem convDimI_swap' {r} (spDims kerDim : DimsI r) (pad : Padding r) :
    convDimI (convDimI spDims kerDim pad) kerDim.rev (pad.revI kerDim)
    =
    spDims := by
  ext <;> (simp[convDimI,DimsI.rev,Padding.revI]; ring)

/--
Index operation during convolution.

Given output tensor index `i` and kernel index `j` return index which should be used to
access input tensor(with dimensions `spDim`) during convolution. -/
def TensorIndex.convMap {kerDim}
    (spDim : Dims r) (pad : Padding r) (i : TensorIndex (convDim spDim kerDim pad))
    (j : TensorIndex kerDim) : TensorIndexI (spDim.pad pad) :=
{
  val := .ofFn (fun a => i[a] + j[a] - pad[a].1)
  bounds := by
    intro d
    have := i.get_le d
    simp_all [convDim,Dims.pad]
    have := j.get_le d
    constructor <;> omega
}

/-- Index operation during convolution.

Given output tensor index `i` and kernel index `j` return index which should be used to
access input tensor(with dimensions `spDim`) during convolution. -/
def TensorIndexI.convMap {kerDim}
    (spDim : DimsI r) (pad : Padding r) (i : TensorIndexI (convDimI spDim kerDim pad))
    (j : TensorIndexI kerDim) : TensorIndexI (spDim.pad pad) :=
{
  val := .ofFn (fun a => i[a] + j[a])
  bounds := by
    intro d
    have := i.get_le d
    simp_all [convDim,convDimI,DimsI.pad]
    have := j.get_le d
    constructor <;> omega
}


def TensorIndexI.InRange {r} {dims : DimsI r} (i : TensorIndexI dims) (dims' : Dims r) : Prop :=
  ∀ (d : Fin r), (0 ≤ i[d]) ∧ (i[d] < dims'[d])

instance {r} {dims : DimsI r} (i : TensorIndexI dims) (dims' : Dims r) :
    Decidable (i.InRange dims') := by unfold TensorIndexI.InRange; infer_instance

def TensorIndexI.cast {r} {dims : DimsI r}
    (i : TensorIndexI dims) {dims' : Dims r} (h : i.InRange dims') : TensorIndex dims' where
  val := i.val
  bounds := h


def TensorIndexI.InRangeI {r} {dims : DimsI r} (i : TensorIndexI dims) (dims' : DimsI r) : Prop :=
  ∀ (d : Fin r), (dims'[d].1 ≤ i[d]) ∧ (i[d] ≤ dims'[d].2)

instance {r} {dims : DimsI r} (i : TensorIndexI dims) (dims' : DimsI r) :
    Decidable (i.InRangeI dims') := by unfold TensorIndexI.InRangeI; infer_instance

def TensorIndexI.castI {r} {dims : DimsI r}
    (i : TensorIndexI dims) {dims' : DimsI r} (h : i.InRangeI dims') : TensorIndexI dims' where
  val := i.val
  bounds := h


variable {R} [RealScalar R] [PlainDataType R]

def DataArrayN.get' {r} {dims : Dims r} {dims' : DimsI r}
    (x : R^[TensorIndex dims]) (i : TensorIndexI dims') : R :=

  if h : i.InRange dims then
    x[i.cast h]
  else
    0

def DataArrayN.get'' {r} {dims dims' : DimsI r}
    (x : R^[TensorIndexI dims]) (i : TensorIndexI dims') : R :=

  if h : i.InRangeI dims then
    x[i.castI h]
  else
    0



def TensorIndexI.convMap' {kerDim : DimsI r}
    (spDim : DimsI r) (pad : Padding r) {outDim : DimsI r} (i : TensorIndexI outDim)
    (j : TensorIndexI kerDim)
    (houtDim : outDim = convDimI spDim kerDim pad := by (try simp_all); (try infer_var))
     : TensorIndexI (spDim.pad pad) :=
{
  val := .ofFn (fun a => i[a] + j[a])
  bounds := by
    intro d
    have := i.get_le d
    simp_all [convDim,convDimI,DimsI.pad]
    have := j.get_le d
    constructor <;> omega
}


-- open TensorIndexI in
-- @[simp]
-- theorem convMapI_swap'
-- {kerDim : DimsI r}
--     (spDim : DimsI r) (pad : Padding r) {outDim : DimsI r} (i : TensorIndexI outDim)
--     (j : TensorIndexI kerDim)
--     (houtDim : outDim = convDimI spDim kerDim pad := by (try simp_all); (try infer_var))
--     (k : TensorIndexI (spDim.pad pad)) :
--   sorry = convMap' (convDimI spDims kerDim pad) (pad.revI kerDim) (k.pad pad) (j.rev)
--        (by ext d <;> simp_all[DimsI.pad]) := sorry


-- {r} (spDims kerDim : DimsI r) (pad : Padding r) :
--     convDimI (convDimI spDims kerDim pad) kerDim.rev (pad.revI kerDim)
--     =
--     spDims := by
--   ext <;> (simp[convDimI,DimsI.rev,Padding.revI]; ring)

#check Finset

#eval ({1,2,3} : Finset ℕ).card


def Vector.removeIds {n α} (a : Vector α n) (ids : Finset (Fin n))
    {m} (h : m = n - ids.card := by (try simp); (try infer_var)) : Vector α m :=
{
  data :=
    let d := ids.map ⟨fun i => i.1, by intro i; aesop⟩
    a.data.zipWithIndex.filterMap (fun (d',i) => if i ∉ d then .some d' else none)
  h_size := sorry
}


abbrev Dims.removeDims {r} (dims : Dims r) (d : Finset (Fin r))
    {s} (h : s = r - d.card := by (try simp); (try infer_var)) : Dims s := dims.removeIds d h


/-- Type used to index dimensions of `r+2` rank tensor with `r` spatial dimensions and batch, feature
dimensions -/
inductive DimId (r : Nat) where
  | batchInputDim
  | featureOutputDim
  | spatialDim (i : Fin r)
deriving IndexType


/-- This equivalence determines which dimensions of `r+2` tensor are spatial, batch and feature. -/
def DimMap (r : ℕ) := DimId r ≃ Fin (r+2)

def DimMap.batchDimId {r} (map : DimMap r) : Fin (r+2) := map.toFun .batchInputDim
def DimMap.featureDimId {r} (map : DimMap r) : Fin (r+2) := map.toFun .featureOutputDim
instance (r) : CoeFun (DimMap r) (fun _ => Fin r → (Fin (r+2))) :=
  ⟨fun f i => f.toFun (.spatialDim i)⟩

/-- Takes dimensions spec of `r+2` rank tensor and returns spec of -/
def DimMap.spatialDims {r} (map : DimMap r) (dims : Dims (r+2)) : Dims r :=
{
  data := .ofFn fun i => dims[map.toFun (.spatialDim i)]
  h_size := by simp
}

def DimMap.batchDim {r} (map : DimMap r) (dims : Dims (r+2)) : ℤ :=
  dims[map.toFun (.batchInputDim)]

def DimMap.featureDim {r} (map : DimMap r) (dims : Dims (r+2)) : ℤ :=
  dims[map.toFun (.featureOutputDim)]


open Set in
def DimMap.indexMap {r} (map : DimMap r) (dims : Dims (r+2))
   {dims'} (hdims' : dims' = map.spatialDims dims := by (try simp); (try infer_var))
   {b} (hb : b = map.batchDim dims := by (try simp); (try infer_var))
   {f} (hf : f = map.featureDim dims := by (try simp); (try infer_var)) :
   TensorIndex dims
   ≃
   Ico 0 b × Ico 0 f × TensorIndex dims' :=
{
  toFun := fun i =>
    (⟨i[map.batchDimId], by rw[hb]; apply i.2⟩,
     ⟨i[map.featureDimId], by rw[hf]; apply i.2⟩,
     ⟨.ofFn fun j => i[map.toFun (.spatialDim j)], by
       intro j
       let j' := map.toFun (.spatialDim j)
       have h := i.2 j'
       simp_all[DimMap.spatialDims]⟩)
  invFun := fun (i,j,k) =>
    ⟨.ofFn fun i =>
       match map.symm i with
       | .batchInputDim => i
       | .featureOutputDim => j
       | .spatialDim i => k[i],
     by
       intro i
       cases (map.symm i)
       · simp; sorry
       · simp; sorry
       · simp; sorry⟩
  left_inv := sorry
  right_inv := sorry
}



section ArraNMissing

instance : HMul (Vector ℤ n) (Vector ℕ+ n) (Vector ℤ n) := ⟨fun x y => x.mapIdx fun i xi => xi * y[i]⟩
instance : HDiv (Vector ℤ n) (Vector ℕ+ n) (Vector ℤ n) := ⟨fun x y => x.mapIdx fun i xi => xi / y[i]⟩
instance : HMod (Vector ℤ n) (Vector ℕ+ n) (Vector ℤ n) := ⟨fun x y => x.mapIdx fun i xi => xi % y[i]⟩
-- instance : HAdd (Vector ℤ n) (Vector ℕ+ n) (Vector ℤ n) := ⟨fun x y => x.mapIdx fun i xi => xi + y[i]⟩
-- instance : HSub (Vector ℤ n) (Vector ℕ+ n) (Vector ℤ n) := ⟨fun x y => x.mapIdx fun i xi => xi - y[i]⟩

instance [Sup α] : Sup (Vector α r) := ⟨fun x y => x.mapIdx fun i xi => xi ⊔ y[i]⟩
instance [Mod α] : Mod (Vector α r) := ⟨fun x y => x.mapIdx fun i xi => xi % y[i]⟩
instance [Div α] : Div (Vector α r) := ⟨fun x y => x.mapIdx fun i xi => xi / y[i]⟩

def Vector.toNat [CoeHTCT α Nat] (x : Vector α n) : Vector ℕ n := .ofFn fun i => x[i]
def Vector.toInt [CoeHTCT α Int] (x : Vector α n) : Vector ℤ n := .ofFn fun i => x[i]


@[simp]
theorem Vector.hmul_apply (x : Vector ℤ n) (y : Vector ℕ+ n) (i : Fin n) :
    (x * y)[i] = x[i] * y[i] := by simp[HMul.hMul, Vector.mapIdx]

@[simp]
theorem Vector.hdiv_apply (x : Vector ℤ n) (y : Vector ℕ+ n) (i : Fin n) :
    (x / y)[i] = x[i] / y[i] := by simp[HDiv.hDiv, Vector.mapIdx]

@[simp]
theorem Vector.hmod_apply (x : Vector ℤ n) (y : Vector ℕ+ n) (i : Fin n) :
    (x % y)[i] = x[i] % y[i] := by simp[HMod.hMod, Vector.mapIdx]

@[simp]
def Dims.rank {r} (dims : Dims r) : ℕ := r
@[simp]
def _root_.SciLean.Vector.size {n α} (a : Vector α n) : ℕ := n


end ArraNMissing
