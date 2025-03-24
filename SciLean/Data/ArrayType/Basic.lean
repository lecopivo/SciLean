import SciLean.Util.SorryProof
import SciLean.Data.ListN
import SciLean.Data.StructType.Basic
import SciLean.Data.IndexType

import SciLean.Meta.SimpAttr

namespace SciLean


/-- This class says that `Cont` behaves like an array with `Elem` values indexed by `Idx`

Examples for `Idx = Fin n` and `Elem = ℝ` are: `ArrayN ℝ n` or `ℝ^{n}`

For `array : Cont` you can:
  1. get values: `ArrayType.get array i : Elem` for `i : Idx`
  2. set values: `ArrayType.set array i x : Cont` for `i : Idx` and `x : Elem`
  3. make new a array: `Indexed.ofFn f : Cont` for `f : Idx → Elem`

Alternative notation:
  1. `array[x]`
  2. in `do` block: `array[x] := y`, `array[x] += y`, ...
  3. `λ [x] => f x` this notation works only if the type `Cont` can be infered from the context
     Common use: `let array : Cont := λ [x] => f x` where the type asscription `: Cont` is important.
-/
class ArrayType (Cont : Type u) (Idx : Type v |> outParam) (Elem : Type w |> outParam) where
  ofFn (f : Idx → Elem) : Cont
  get (cont : Cont) (i : Idx) : Elem
  set (cont : Cont) (i : Idx) (xi : Elem) : Cont
  modify (cont : Cont) (i : Idx) (f : Elem → Elem) : Cont
  get_ofFn : Function.LeftInverse get ofFn
  ofFn_get : Function.RightInverse ofFn get
  get_set_eq : ∀ c i xi, get (set c i xi) i = xi
  get_set_neq : ∀ c i i' xi, i≠i' → get (set c i xi) i' = get c i'
  modify_set : ∀ c i f, modify c i f = set c i (f (get c i))

attribute [simp,simp_core] ArrayType.get_set_eq ArrayType.get_set_neq

-- instance {Cont Idx Elem} [ArrayType Cont Idx Elem] : StructType Cont Idx (fun _ => Elem) where
--   structProj := fun c i => ArrayType.get c i
--   structMake := ArrayType.ofFn
--   structModify := fun i f c => ArrayType.modify c i f
--   left_inv := sorry_proof
--   right_inv := sorry_proof
--   structProj_structModify := sorry_proof
--   structProj_structModify' := sorry_proof

instance {Cont Idx Elem} [ArrayType Cont Idx Elem] : StructType Cont (Idx×Unit) (fun _ => Elem) where
  structProj := fun c (i,_) => ArrayType.get c i
  structMake := fun f => ArrayType.ofFn (fun i => f (i,()))
  structModify := fun (i,_) f c => ArrayType.modify c i f
  left_inv := sorry_proof
  right_inv := sorry_proof
  structProj_structModify := sorry_proof
  structProj_structModify' := sorry_proof


namespace ArrayType

set_option deprecated.oldSectionVars true

variable
  {Cont : Type _} {Idx : Type _ |> outParam} {Elem : Type _ |> outParam}
  {n} [IndexType Idx n] [Fold Idx] [outParam <| DecidableEq Idx]
  [ArrayType Cont Idx Elem]

@[ext]
theorem ext (x y : Cont) : (∀ i, get x i = get y i) → x = y := by sorry_proof

@[simp,simp_core]
theorem eta (cont : Cont) : (ofFn fun i => get cont i) = cont := sorry_proof

def mapMono (f : Elem → Elem) (cont : Cont) : Cont :=
  IndexType.fold .full cont (fun i c => modify c i f)

def mapIdxMono (f : Idx → Elem → Elem) (cont : Cont) : Cont :=
  IndexType.fold .full cont (fun i c => modify c i (f i))

@[simp,simp_core]
theorem get_mapMono (f : Elem → Elem) (cont : Cont) (i : Idx) :
    get (mapMono f cont) i = f (get cont i) := sorry_proof

@[simp,simp_core]
theorem get_mapIdxMono (f : Idx → Elem → Elem) (cont : Cont) (i : Idx) :
    get (mapIdxMono f cont) i = f i (get cont i) := sorry_proof

@[simp,simp_core]
theorem get_ofFn' (f : Idx → Elem) :
  get (ofFn (Cont:=Cont) f) = f := sorry_proof

@[simp,simp_core]
theorem get_modify_eq (xs : Cont) (f : Elem → Elem) (i : Idx) :
  get (modify xs i f) i = f (get xs i) := by rw[modify_set]; simp[get_set_eq]

@[simp,simp_core]
theorem get_modify_neq (xs : Cont) (f : Elem → Elem) (i j : Idx) (h : i ≠ j) :
  get (modify xs i f) j = get xs j := by rw[modify_set]; simp[get_set_neq,h]


instance (priority:=low) [ArrayType Cont Idx Elem] [ToString Elem]
    {n} [IndexType Idx n] [Fold Idx] :
    ToString (Cont) := ⟨λ x => Id.run do
  let mut fst := true
  let mut s := "⊞["
  for i in fullRange Idx do
    if fst then
      s := s ++ toString (get x i)
      fst := false
    else
      s := s ++ ", " ++ toString (get x i)
  s ++ "]"⟩

-- /-- Converts array to ArrayType -/
-- def _root_.Array.toArrayType {Elem} (Cont : Type u) (Idx : Type v)
--   {n} [IndexType Idx n] [ArrayType Cont Idx Elem]
--   (a : Array Elem) (h : n = a.size) : Cont :=
--   ArrayType.ofFn fun (i : Idx) => a[h ▸ IndexType.toFin i]

-- /-- Converts ListN to ArrayType

--   WARNING: Does not do what expected for lists of size bigger or equal then USize.size
--     For example, array of size USize.size is converted to an array of size zero
--   -/
-- def _root_.ListN.toArrayType {n Elem} (Cont : Type) [ArrayType Cont (SciLean.Idx (n.toUSize)) Elem]
--   (l : ListN Elem n) : Cont :=
--   introElem fun i => l.toArray[i.1.toNat]'sorry_proof

instance [StructType Elem I ElemI] : StructType Cont (Idx×I) (fun (_,i) => ElemI i) where
  structProj := fun x (i,j) => structProj (get x i) j
  structMake := fun f => ofFn fun i => structMake fun j => f (i,j)
  structModify := fun (i,j) f x => modify x i (fun xi => structModify j f xi)
  left_inv := by intro x; simp
  right_inv := by intro x; simp
  structProj_structModify := by intro x; simp
  structProj_structModify' := by intro (i,j) (i',j') _ _ _; sorry_proof



section Operations

  scoped instance (priority:=low) [Add Elem] : Add Cont := ⟨λ f g => mapIdxMono (λ x fx => fx + get g x) f⟩
  scoped instance (priority:=low) [Sub Elem] : Sub Cont := ⟨λ f g => mapIdxMono (λ x fx => fx - get g x) f⟩
  -- instance (priority:=low) [Mul Elem] : Mul Cont := ⟨λ f g => mapIdxMono (λ x fx => fx * get g x) f⟩
  -- instance (priority:=low) [Div Elem] : Div Cont := ⟨λ f g => mapIdxMono (λ x fx => fx / get g x) f⟩

  -- instance (priority:=low) {R} [HMul R Elem Elem] : HMul R Cont Cont := ⟨λ r f => map (λ fx => r*(fx : Elem)) f⟩
  scoped instance (priority:=low) {R} [SMul R Elem] : SMul R Cont := ⟨λ r f => mapMono (λ fx => r•(fx : Elem)) f⟩

  scoped instance (priority:=low) [Neg Elem] : Neg Cont := ⟨λ f => mapMono (λ fx => -(fx : Elem)) f⟩
  -- instance (priority:=low) [Inv Elem] : Inv Cont := ⟨λ f => mapMono (λ fx => (fx : Elem)⁻¹) f⟩

  scoped instance (priority:=low) [One Elem]  : One Cont  := ⟨ofFn fun (_ : Idx) => 1⟩
  scoped instance (priority:=low) [Zero Elem] : Zero Cont := ⟨ofFn fun (_ : Idx) => 0⟩

  scoped instance (priority:=low) [LT Elem] : LT Cont := ⟨λ f g => ∀ x, get f x < get g x⟩
  scoped instance (priority:=low) [LE Elem] : LE Cont := ⟨λ f g => ∀ x, get f x ≤ get g x⟩

  scoped instance (priority:=low) [DecidableEq Elem] : DecidableEq Cont :=
    λ f g => Id.run do
      let mut eq : Bool := true
      for x in fullRange Idx do
        if get f x ≠ get g x then
          eq := false
          break
      if eq then isTrue sorry_proof else isFalse sorry_proof

  scoped instance (priority:=low) [LT Elem] [∀ x y : Elem, Decidable (x < y)] (f g : Cont) :
      Decidable (f < g) := Id.run do
    let mut lt : Bool := true
    for x in fullRange Idx do
      if ¬(get f x < get g x) then
        lt := false
        break
    if lt then isTrue sorry_proof else isFalse sorry_proof

  scoped instance (priority:=low) [LE Elem] [∀ x y : Elem, Decidable (x ≤ y)] (f g : Cont) :
      Decidable (f ≤ g) := Id.run do
    let mut le : Bool := true
    for x in fullRange Idx do
      if ¬(get f x ≤ get g x) then
        le := false
        break
    if le then isTrue sorry_proof else isFalse sorry_proof

  --TODO: all of these theorem should be autogenerated based on IsAddGroupHom
  @[simp, simp_core]
  theorem add_ofFn [Add Elem] (f g: Idx → Elem)
    : ofFn (Cont:=Cont) f + ofFn (Cont:=Cont) g
      =
      ofFn fun i => f i + g i  := by apply ArrayType.ext (Idx:=Idx); simp[HAdd.hAdd, Add.add]

  @[simp, simp_core]
  theorem sub_ofFn [Sub Elem] (f g: Idx → Elem)
    : ofFn (Cont:=Cont) f - ofFn (Cont:=Cont) g
      =
      ofFn fun i => f i - g i  := by apply ArrayType.ext (Idx:=Idx); simp[HSub.hSub, Sub.sub]

  @[simp, simp_core]
  theorem neg_ofFn [Neg Elem] (f: Idx → Elem)
    : - ofFn (Cont:=Cont) f
      =
      ofFn fun i => - f i  := by apply ArrayType.ext (Idx:=Idx); simp[Neg.neg]

  @[simp, simp_core]
  theorem smul_ofFn [SMul K Elem] (f : Idx → Elem) (a : K)
    : a • ofFn (Cont:=Cont) f
      =
      ofFn fun i => a • f i := by apply ArrayType.ext (Idx:=Idx); simp[HSMul.hSMul, SMul.smul];

  -- @[simp, simp_core, sum_push]
  -- theorem sum_ofFn [AddCommMonoid Elem] {ι} [IndexType ι] (f : ι → Idx → Elem)
  --   : ∑ j, ofFn (Cont:=Cont) (fun i => f j i)
  --     =
  --     ofFn fun i => ∑ j, f j i
  --   := sorry_proof

  -- @[sum_pull]
  -- theorem ofFn_sum [AddCommMonoid Elem] {ι} [IndexType ι] (f : ι → Idx → Elem)
  --   : ofFn (Cont:=Cont) (fun i => ∑ j, f j i)
  --     =
  --     ∑ j, ofFn (Cont:=Cont) (fun i => f j i) := by simp only [sum_ofFn]

  @[simp, simp_core]
  theorem add_get [Add Elem] (x y : Cont) (i : Idx) :
      get (x + y) i = get x i + get y i := by simp[HAdd.hAdd,Add.add]

  @[simp, simp_core]
  theorem sub_get [Sub Elem] (x y : Cont) (i : Idx) :
      get (x - y) i  = get x i - get y i := by simp[HSub.hSub,Sub.sub]

  -- @[simp, simp_core]
  -- theorem mul_get [Mul Elem] (x y : Cont) (i : Idx) :
  --     get (x * y) i  = get x i * get y i := by simp[HMul.hMul,Mul.mul]

  -- @[simp, simp_core]
  -- theorem div_get [Div Elem] (x y : Cont) (i : Idx) :
  --     get (x / y) i  = get x i / get y i := by simp[HDiv.hDiv,Div.div]

  @[simp, simp_core]
  theorem smul_get {R} [SMul R Elem] (r : R) (x : Cont) (i : Idx) :
      get (r • x) i  = r • get x i := by simp[HSMul.hSMul,SMul.smul]

  @[simp, simp_core]
  theorem neg_get [Neg Elem] (x : Cont) (i : Idx) :
      get (- x) i  = - get x i := by simp[Neg.neg]

  @[simp, simp_core]
  theorem one_get [One Elem] (i : Idx) :
      get (1 : Cont) i  = 1 := by simp[One.one,OfNat.ofNat]

  @[simp, simp_core]
  theorem zero_get [Zero Elem] (i : Idx) :
      get (0 : Cont) i  = 0 := by simp[Zero.zero,OfNat.ofNat]

end Operations


section UsefulFunctions

variable [LT Elem] [∀ x y : Elem, Decidable (x < y)] [Inhabited Idx]

def argMaxCore (cont : Cont) : Idx × Elem :=
  IndexType.reduceD
    .full
    (fun i => (i,get cont i))
    (fun (i,e) (i',e') => if e < e' then (i',e') else (i,e))
    (default, get cont default)

def max (cont : Cont) : Elem :=
  IndexType.reduceD
    .full
    (fun i => get cont i)
    (fun e e' => if e < e' then e' else e)
    (get cont default)

def idxMax (cont : Cont) : Idx := (argMaxCore cont).1


def argMinCore (cont : Cont ) : Idx × Elem :=
  IndexType.reduceD
    .full
    (fun i => (i,get cont i))
    (fun (i,e) (i',e') => if e' < e then (i',e') else (i,e))
    (default, get cont default)

def min (cont : Cont) : Elem :=
  IndexType.reduceD
    .full
    (fun i => get cont i)
    (fun e e' => if e < e' then e' else e)
    (get cont default)

def idxMin (cont : Cont) : Idx := (argMinCore cont).1

end UsefulFunctions

end ArrayType

-- namespace ArrayType

--   variable {Cont : Nat → Type} {Elem : Type |> outParam}
--   variable [LinearArrayType Cont Elem]

--   def empty : Cont 0 := Indexed.ofFn λ i =>
--     absurd (a := ∃ n : Nat, n < 0)
--            (Exists.intro i.1 i.2)
--            (by intro h; have h' := h.choose_spec; cases h'; done)

--   def split {n m : Nat} (x : Cont (n+m)) : Cont n × Cont m :=
--     (Indexed.ofFn λ i => x[⟨i.1,sorry_proof⟩],
--      Indexed.ofFn λ i => x[⟨i.1+n,sorry_proof⟩])

--   def append {n m : Nat} (x : Cont n) (y : Cont m) : Cont (n+m) :=
--     Indexed.ofFn λ i =>
--       if i.1 < n
--       then x[⟨i.1,sorry_proof⟩]
--       else y[⟨i.1-n, sorry_proof⟩]

-- end ArrayType
