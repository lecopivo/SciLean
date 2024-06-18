import SciLean.Core.Objects.FinVec
import SciLean.Core.FunctionPropositions.IsLinearMap

import SciLean.Tactic.FunTrans.Attr
import SciLean.Tactic.FunTrans.Elab

open SciLean LeanColls

variable
  {K : Type} [RCLike K]
  {IX : Type} [IndexType IX] [LawfulIndexType IX] [DecidableEq IX] {X : Type _} [FinVec IX K X]
  {IY : Type} [IndexType IY] [LawfulIndexType IY] [DecidableEq IY] {Y : Type _} [FinVec IY K Y]
  {IZ : Type} [IndexType IZ] [LawfulIndexType IZ] [DecidableEq IZ] {Z : Type _} [FinVec IZ K Z]

namespace SciLean

-- having index sets unverse polymorphic trips up simplifier
def mulMat (A : IZ → IY → K) (B : IY → IX → K) (i : IZ) (j : IX) : K := ∑ k, A i k * B k j
def mulVec (A : IY → IX → K) (x : IX → K) (i : IY) : K := ∑ j, A i j * x j

variable (K)
@[fun_trans]
def toMatrix (f : X → Y) (i : IY) (j : IX) : K := ℼ i (f (ⅇ j))

namespace toMatrix
--------------------------------------------------------------------------------

@[fun_trans]
theorem id_rule
  : toMatrix K (fun x : X => x)
    =
    fun i j => if i = j then 1 else 0 :=
by
  unfold toMatrix
  simp

@[fun_trans]
theorem const_zero_rule
  : toMatrix K (fun _ : X => (0 : Y))
    =
    fun i j => 0 :=
by
  unfold toMatrix
  simp

@[fun_trans]
theorem comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : IsLinearMap K f) (hg : IsLinearMap K g)
  : toMatrix K (fun x => f (g x))
    =
    mulMat (toMatrix K f) (toMatrix K g) :=
by
  unfold toMatrix mulMat
  funext i j
  symm
  calc ∑ k, ℼ i (f ⅇ k) * ℼ k (g ⅇ j)
    _ = ℼ i (f (∑ k, ℼ k (g ⅇ j) • ⅇ k)) := by sorry_proof
    _ = ℼ i (f (g ⅇ j)) := by sorry_proof -- simp[FinVec.is_basis]

@[fun_trans]
theorem apply_rule [IndexType ι] [LawfulIndexType ι] [DecidableEq ι] (i : ι)
  : toMatrix K (fun f : ι → X => f i)
    =
    fun ix (j,jx) => (if j = i ∧ jx = ix then 1 else 0) :=
by
  funext ix (j,jx)
  simp[toMatrix,Basis.basis,Basis.proj]
  sorry_proof


end toMatrix

open SciLean

@[fun_trans]
theorem Prod.mk.arg_fstsnd.toMatrix_rule
  (g : X → Y) (f : X → Z)
  : toMatrix K (fun x => (g x, f x))
    =
    fun i jx =>
      match i with
      | .inl iy => toMatrix K g iy jx
      | .inr iz => toMatrix K f iz jx :=
    -- this would be nice notation inspired by dex-lang
    -- fun (iy|iz) jx => (toMatrix K g iy jx | toMatrix K f iz jx) :=
by
  simp[toMatrix,Basis.basis,Basis.proj]
  rfl


@[fun_trans]
theorem Prod.fst.arg_self.toMatrix_rule
  (f : X → Y×Z) (hf : IsLinearMap K f)
  : toMatrix K (fun x => (f x).1)
    =
    fun iy ix => toMatrix K f (.inl iy) ix :=
by
  unfold toMatrix
  simp[Basis.basis,Basis.proj]


@[fun_trans]
theorem Prod.snd.arg_self.toMatrix_rule
  (f : X → Y×Z) (hf : IsLinearMap K f)
  : toMatrix K (fun x => (f x).2)
    =
    fun iz ix => toMatrix K f (.inr iz) ix :=
by
  unfold toMatrix
  simp[Basis.basis,Basis.proj]


@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.toMatrix_rule
  (f g : X → Y) (hf : IsLinearMap K f) (hg : IsLinearMap K g)
  : (toMatrix K fun x => f x + g x)
    =
    fun i j => toMatrix K f i j + toMatrix K g i j :=
by
  unfold toMatrix
  simp[(Basis.proj.arg_x.IsLinearMap_rule _).map_add]


@[fun_trans]
theorem HSub.hSub.arg_a0a1.toMatrix_rule
  (f g : X → Y) (hf : IsLinearMap K f) (hg : IsLinearMap K g)
  : (toMatrix K fun x => f x - g x)
    =
    fun i j => toMatrix K f i j - toMatrix K g i j :=
by
  unfold toMatrix
  simp[(Basis.proj.arg_x.IsLinearMap_rule _).map_sub]


@[fun_trans]
theorem Neg.neg.arg_a0.toMatrix_rule
  (f : X → Y) (hf : IsLinearMap K f)
  : (toMatrix K fun x => - f x)
    =
    fun i j => - toMatrix K f i j :=
by
  unfold toMatrix
  simp[(Basis.proj.arg_x.IsLinearMap_rule _).map_neg]


@[fun_trans]
theorem HSMul.hSMul.arg_a1.toMatrix_rule
  (k : K) (f : X → Y) (hf : IsLinearMap K f)
  : (toMatrix K fun x => k • f x)
    =
    fun i j => k * toMatrix K f i j :=
by
  unfold toMatrix
  simp[(Basis.proj.arg_x.IsLinearMap_rule _).map_smul]


@[fun_trans]
theorem HSMul.hSMul.arg_a0.toMatrix_rule
  (f : X → K) (y : Y) (hf : IsLinearMap K f)
  : (toMatrix K fun x => f x • y)
    =
    fun i j => f (ⅇ j) * ℼ i y :=
by
  unfold toMatrix
  simp[(Basis.proj.arg_x.IsLinearMap_rule _).map_smul]


@[fun_trans]
theorem SciLean.EnumType.sum.arg_f.toMatrix_rule [IndexType ι]
  (f : X → ι → Y) (hf : ∀ i, IsLinearMap K (f · i))
  : toMatrix K (fun x => ∑ i, f x i)
    =
    fun i j => ∑ i', toMatrix K (f · i') i j :=
by
  unfold toMatrix
  simp
  sorry_proof


@[fun_trans]
theorem SciLean.mulVec.arg_x_i.toMatrix_rule
  (A : IY → IX → K) (x : W → IX → K) (hx : ∀ ix, IsLinearMap K (x · ix))
  : toMatrix K (fun x' iy => mulVec A (x x') iy)
    =
    fun _ iw => ∑ ix', A iy ix' * x (ⅇ iw) ix' :=
by
  sorry_proof
