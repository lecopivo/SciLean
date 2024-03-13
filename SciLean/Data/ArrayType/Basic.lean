import SciLean.Util.SorryProof
import SciLean.Data.ListN
import SciLean.Data.StructType.Basic
import SciLean.Data.Function
import LeanColls

namespace SciLean

open LeanColls



/-- This class says that `Cont` behaves like an array with `Elem` values indexed by `Idx`

Examples for `Idx = Fin n` and `Elem = ℝ` are: `ArrayN ℝ n` or `ℝ^{n}`

For `array : Cont` you can:
  1. get values: `Indexed.get array i : Elem` for `i : Idx`
  2. set values: `Indexed.set array i x : Cont` for `i : Idx` and `x : Elem`
  3. make new a array: `Indexed.ofFn f : Cont` for `f : Idx → Elem`

Alternative notation:
  1. `array[x]`
  2. in `do` block: `array[x] := y`, `array[x] += y`, ...
  3. `λ [x] => f x` this notation works only if the type `Cont` can be infered from the context
     Common use: `let array : Cont := λ [x] => f x` where the type asscription `: Cont` is important.
-/
class ArrayType (Cont : Type u) (Idx : Type v |> outParam) (Elem : Type w |> outParam)
    extends Indexed.{u,v,w,w} Cont Idx Elem, LawfulIndexed.{u,v,w,w} Cont Idx Elem where
  get_injective : Function.Injective (fun (c : Cont) i => c[i])


instance {Cont Idx Elem} [ArrayType Cont Idx Elem] : StructType Cont Idx (fun _ => Elem) where
  structProj := fun c i => c[i]
  structMake := Indexed.ofFn
  structModify := fun i f c => Indexed.update c i f
  left_inv := sorry_proof
  right_inv := sorry_proof
  structProj_structModify := sorry_proof
  structProj_structModify' := sorry_proof


namespace ArrayType

variable
  {Cont : Type _} {Idx : Type _ |> outParam} {Elem : Type _ |> outParam}
  [IndexType Idx] [outParam <| DecidableEq Idx] [LawfulIndexType Idx]
  [ArrayType Cont Idx Elem]

@[ext]
theorem ext (x y : Cont) : (∀ i, x[i] = y[i]) → x = y := by sorry_proof

@[simp]
theorem eta (cont : Cont) : (Indexed.ofFn fun i => cont[i]) = cont := sorry_proof

def mapMono (f : Elem → Elem) (cont : Cont) : Cont :=
  Fold.fold (IndexType.univ Idx) (fun c i => Indexed.update c i f) cont

def mapMonoIdx (f : Idx → Elem → Elem) (cont : Cont) : Cont :=
  Fold.fold (IndexType.univ Idx) (fun c i => Indexed.update c i (f i)) cont

@[simp]
theorem getElem_mapMono (f : Elem → Elem) (cont : Cont) (i : Idx) :
    (mapMono f cont)[i] = f cont[i] := sorry_proof

@[simp]
theorem getElem_mapMonoIdx (f : Idx → Elem → Elem) (cont : Cont) (i : Idx) :
    (mapMonoIdx f cont)[i] = f i cont[i] := sorry_proof

@[simp]
theorem getElem_map (f : Elem → Elem) (cont : Cont) (i : Idx) :
    (mapMono f cont)[i] = f cont[i] := sorry_proof

instance (priority:=low) [ArrayType Cont Idx Elem] [ToString Elem] [IndexType Idx] :
    ToString (Cont) := ⟨λ x => Id.run do
  let mut fst := true
  let mut s := "⊞["
  for i in IndexType.univ Idx do
    if fst then
      s := s ++ toString x[i]
      fst := false
    else
      s := s ++ ", " ++ toString x[i]
  s ++ "]"⟩

/-- Converts array to ArrayType -/
def _root_.Array.toArrayType {Elem} (Cont : Type u) (Idx : Type v) [IndexType Idx] [Indexed Cont Idx Elem]
  (a : Array Elem) (h : IndexType.card Idx = a.size) : Cont :=
  Indexed.ofFn fun (i : Idx) => a[h ▸ IndexType.toFin i]

-- /-- Converts ListN to ArrayType

--   WARNING: Does not do what expected for lists of size bigger or equal then USize.size
--     For example, array of size USize.size is converted to an array of size zero
--   -/
-- def _root_.ListN.toArrayType {n Elem} (Cont : Type) [ArrayType Cont (SciLean.Idx (n.toUSize)) Elem]
--   (l : ListN Elem n) : Cont :=
--   introElem fun i => l.toArray[i.1.toNat]'sorry_proof

instance [StructType Elem I ElemI] : StructType Cont (Idx×I) (fun (_,i) => ElemI i) where
  structProj := fun x (i,j) => structProj x[i] j
  structMake := fun f => Indexed.ofFn fun i => structMake fun j => f (i,j)
  structModify := fun (i,j) f x => Indexed.update x i (fun xi => structModify j f xi)
  left_inv := by intro x; simp
  right_inv := by intro x; simp
  structProj_structModify := by intro x; simp
  structProj_structModify' := by intro (i,j) (i',j') _ _ _; sorry_proof



section Operations

  instance (priority:=low) [Add Elem] : Add Cont := ⟨λ f g => mapMonoIdx (λ x fx => fx + g[x]) f⟩
  instance (priority:=low) [Sub Elem] : Sub Cont := ⟨λ f g => mapMonoIdx (λ x fx => fx - g[x]) f⟩
  instance (priority:=low) [Mul Elem] : Mul Cont := ⟨λ f g => mapMonoIdx (λ x fx => fx * g[x]) f⟩
  instance (priority:=low) [Div Elem] : Div Cont := ⟨λ f g => mapMonoIdx (λ x fx => fx / g[x]) f⟩

  -- instance (priority:=low) {R} [HMul R Elem Elem] : HMul R Cont Cont := ⟨λ r f => map (λ fx => r*(fx : Elem)) f⟩
  instance (priority:=low) {R} [SMul R Elem] : SMul R Cont := ⟨λ r f => mapMono (λ fx => r•(fx : Elem)) f⟩

  instance (priority:=low) [Neg Elem] : Neg Cont := ⟨λ f => mapMono (λ fx => -(fx : Elem)) f⟩
  instance (priority:=low) [Inv Elem] : Inv Cont := ⟨λ f => mapMono (λ fx => (fx : Elem)⁻¹) f⟩

  instance (priority:=low) [One Elem]  : One Cont  := ⟨Indexed.ofFn fun (_ : Idx) => 1⟩
  instance (priority:=low) [Zero Elem] : Zero Cont := ⟨Indexed.ofFn fun (_ : Idx) => 0⟩

  instance (priority:=low) [LT Elem] : LT Cont := ⟨λ f g => ∀ x, f[x] < g[x]⟩
  instance (priority:=low) [LE Elem] : LE Cont := ⟨λ f g => ∀ x, f[x] ≤ g[x]⟩

  instance (priority:=low) [DecidableEq Elem] : DecidableEq Cont :=
    λ f g => Id.run do
      let mut eq : Bool := true
      for x in IndexType.univ Idx do
        if f[x] ≠ g[x] then
          eq := false
          break
      if eq then isTrue sorry_proof else isFalse sorry_proof

  instance (priority:=low) [LT Elem] [∀ x y : Elem, Decidable (x < y)] (f g : Cont) :
      Decidable (f < g) := Id.run do
    let mut lt : Bool := true
    for x in IndexType.univ Idx do
      if ¬(f[x] < g[x]) then
        lt := false
        break
    if lt then isTrue sorry_proof else isFalse sorry_proof

  instance (priority:=low) [LE Elem] [∀ x y : Elem, Decidable (x ≤ y)] (f g : Cont) :
      Decidable (f ≤ g) := Id.run do
    let mut le : Bool := true
    for x in IndexType.univ Idx do
      if ¬(f[x] ≤ g[x]) then
        le := false
        break
    if le then isTrue sorry_proof else isFalse sorry_proof

  @[simp, ftrans_simp]
  theorem add_ofFn [Add Elem] (f g: Idx → Elem)
    : Indexed.ofFn (C:=Cont) f + Indexed.ofFn (C:=Cont) g
      =
      Indexed.ofFn fun i => f i + g i  := by apply ArrayType.ext (Idx:=Idx); simp[HAdd.hAdd, Add.add]

  @[simp, ftrans_simp]
  theorem sub_ofFn [Sub Elem] (f g: Idx → Elem)
    : Indexed.ofFn (C:=Cont) f - Indexed.ofFn (C:=Cont) g
      =
      Indexed.ofFn fun i => f i - g i  := by apply ArrayType.ext (Idx:=Idx); simp[HSub.hSub, Sub.sub]

  @[simp, ftrans_simp]
  theorem neg_ofFn [Neg Elem] (f: Idx → Elem)
    : - Indexed.ofFn (C:=Cont) f
      =
      Indexed.ofFn fun i => - f i  := by apply ArrayType.ext (Idx:=Idx); simp[Neg.neg]

  @[simp, ftrans_simp]
  theorem smul_ofFn [SMul K Elem] (f : Idx → Elem) (a : K)
    : a • Indexed.ofFn (C:=Cont) f
      =
      Indexed.ofFn fun i => a • f i := by apply ArrayType.ext (Idx:=Idx); simp[HSMul.hSMul, SMul.smul];

  @[simp, ftrans_simp]
  theorem sum_ofFn [AddCommMonoid Elem] {ι} [IndexType ι] (f : ι → Idx → Elem)
    : ∑ j, Indexed.ofFn (C:=Cont) (fun i => f j i)
      =
      Indexed.ofFn fun i => ∑ j, f j i
    := sorry_proof

  @[simp, ftrans_simp]
  theorem add_get [Add Elem] (x y : Cont) (i : Idx) :
      (x + y)[i] = x[i] + y[i] := by simp[HAdd.hAdd,Add.add]

  @[simp, ftrans_simp]
  theorem sub_get [Sub Elem] (x y : Cont) (i : Idx) :
      (x - y)[i] = x[i] - y[i] := by simp[HSub.hSub,Sub.sub]

  @[simp, ftrans_simp]
  theorem mul_get [Mul Elem] (x y : Cont) (i : Idx) :
      (x * y)[i] = x[i] * y[i] := by simp[HMul.hMul,Mul.mul]

  @[simp, ftrans_simp]
  theorem div_get [Div Elem] (x y : Cont) (i : Idx) :
      (x / y)[i] = x[i] / y[i] := by simp[HDiv.hDiv,Div.div]

  @[simp, ftrans_simp]
  theorem smul_get {R} [SMul R Elem] (r : R) (x : Cont) (i : Idx) :
      (r • x)[i] = r • x[i] := by simp[HSMul.hSMul,SMul.smul]

  @[simp, ftrans_simp]
  theorem neg_get [Neg Elem] (x : Cont) (i : Idx) :
      (- x)[i] = - x[i] := by simp[Neg.neg]

  @[simp, ftrans_simp]
  theorem one_get [One Elem] (i : Idx) :
      (1 : Cont)[i] = 1 := by simp[One.one,OfNat.ofNat]

  @[simp, ftrans_simp]
  theorem zero_get [Zero Elem] (i : Idx) :
      (0 : Cont)[i] = 0 := by simp[Zero.zero,OfNat.ofNat]

end Operations


section UsefulFunctions

variable [LT Elem] [∀ x y : Elem, Decidable (x < y)] [Inhabited Idx]

def argMaxCore (cont : Cont) : Idx × Elem :=
  IndexType.reduceD
    (fun i => (i,cont[i]))
    (fun (i,e) (i',e') => if e < e' then (i',e') else (i,e))
    (default, cont[default])

def max (cont : Cont) : Elem :=
  Function.reduceD
    (fun i => cont[i])
    (fun e e' => if e < e' then e' else e)
    (cont[default])

def idxMax (cont : Cont) : Idx := (argMaxCore cont).1


def argMinCore (cont : Cont ) : Idx × Elem :=
  Function.reduceD
    (fun i => (i,cont[i]))
    (fun (i,e) (i',e') => if e' < e then (i',e') else (i,e))
    (default, cont[default])

def min (cont : Cont) : Elem :=
  Function.reduceD
    (fun i => cont[i])
    (fun e e' => if e < e' then e' else e)
    (cont[default])

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
