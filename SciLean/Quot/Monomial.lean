import SciLean.Quot.FreeMonoid
import SciLean.Quot.QuotQ
 
inductive List.Sorted {X : Type u} [LT X] : List X → Prop where
| empty : Sorted []
| singl (x : X) : Sorted [x]
| head  (x y : X) (ys : List X) (h : (x < y) ∨ (x = y)) (h' : Sorted (y :: ys)) 
        : Sorted (x :: y :: ys)

inductive List.StrictlySorted {X : Type u} [LT X] : List X → Prop where
| empty : StrictlySorted []
| singl (x : X) : StrictlySorted [x]
| head  (x y : X) (ys : List X) (h : x < y) 
        (h' : StrictlySorted (y :: ys)) 
        : StrictlySorted (x :: y :: ys)

--- Sorts list and returns the number of transpositions, bool indicates repeated element
partial def List.bubblesortTransNum {α} [LT α] [DecidableCp α] (l : List α) : List α × ℕ × Bool :=
  match l with
  | [] => ([], 0, false)
  | x :: xs => 
    match xs.bubblesortTransNum with
    | ([], n, b) => ([x], n, b)
    | (y :: ys, n, b) => 
      match decCp x y with
      | cpEq h => (x :: y :: ys, n, true)
      | cpLt h => (x :: y :: ys, n, b)
      | cpGt h => 
        let (xys, n', b') := (x :: ys).bubblesortTransNum
        (y :: xys, n + n' + 1, b ∨ b')

def List.bubblesort {α} [LT α] [DecidableCp α] (l : List α) : List α 
  := l.bubblesortTransNum.1

namespace SciLean

open Quot'

class Rank (α : Type u) where
  rank : α → ℕ

def napply (f : α → α) (n : ℕ) (a : α) : α :=
  match n with
  | 0 => a
  | n+1 => napply f n (f a)

export Rank (rank)


class Monomial (M) (K : Type v) (X : Type u) extends HMul K M M, Mul M where
  intro : K → X → M
  base : M → X
  coef : M → K

namespace Monomial 

  structure Repr (K : Type v) (ι : Type u) where
    coef : K
    base : FreeMonoid ι

  instance {K ι} [ToString K] [ToString ι] : ToString (Repr K ι) :=
   ⟨λ x => s!"{x.coef}*{x.base}"⟩

  instance {K ι} [Mul K] : Mul (Repr K ι) := 
    ⟨λ x y => ⟨x.coef * y.coef, x.base * y.base⟩⟩

  instance {K ι} [Mul K] : HMul K (Repr K ι) (Repr K ι) := 
    ⟨λ a x => ⟨a * x.coef, x.base⟩⟩
  instance {K ι} [Mul K] : HMul (Repr K ι) K (Repr K ι) := 
    ⟨λ x a => ⟨x.coef * a, x.base⟩⟩

  -- def Repr.rank {K X} (x : Repr K X) : Nat := x.base.rank

  -- Makes only multiplication on X 
  inductive FreeEq (K ι) [Zero K] : Repr K ι → Repr K ι → Prop where
    | refl (x : Repr K ι) : FreeEq K ι x x
    | zero_coeff (x y : FreeMonoid ι) : FreeEq K ι ⟨0, x⟩ ⟨0, y⟩

  inductive SymEq (K ι) [Zero K] : Repr K ι → Repr K ι → Prop where
    | eq (x y : Repr K ι) (h : FreeEq K ι x y) : SymEq K ι x y
    | sym_mul (c : K) (x y : FreeMonoid ι) : SymEq K ι ⟨c, x * y⟩ ⟨c, y * x⟩

  inductive AltEq (K ι) [Zero K] [Neg K] : Repr K ι → Repr K ι → Prop where
    | eq (x y : Repr K ι) (h : FreeEq K ι x y) : AltEq K ι x y
    | alt_mul (c : K) (x y : FreeMonoid ι) : AltEq K ι ⟨c, x * y⟩ ⟨napply Neg.neg (x.rank * y.rank) c, y * x⟩

  instance {K ι} [Zero K] : QForm (FreeEq K ι) :=
  {
    RedForm := λ lvl x => 
      match lvl with
      | redLvl n => True
      | normLvl => (x.coef = 0 → x.base = 1)
    redform_norm := sorry
    redform_zero := sorry
    redform_succ := sorry
    redform_inf  := sorry
  }

  instance {K ι} [LT ι] [Zero K] : QForm (SymEq K ι) :=
  {
    RedForm := λ lvl x => 
      match lvl with
      | redLvl 0 => True
      | redLvl n => x.base.1.Sorted
      | normLvl => x.base.1.Sorted ∧ (x.coef = 0 → x.base = 1)
    redform_norm := sorry
    redform_zero := sorry
    redform_succ := sorry
    redform_inf  := sorry
  }

  instance {K ι} [LT ι] [Zero K] [Neg K] : QForm (AltEq K ι) :=
  {
    RedForm := λ lvl x => 
      match lvl with
      | redLvl 0 => True
      | redLvl n => x.base.1.StrictlySorted
      | normLvl => x.base.1.StrictlySorted ∧ (x.coef = 0 → x.base = 1)
    redform_norm := sorry
    redform_zero := sorry
    redform_succ := sorry
    redform_inf  := sorry
  }

  instance {K ι} [Zero K] : QReduce (FreeEq K ι) rawLvl :=
  {
    reduce := λ x => x
    is_reduce := sorry
    eq_reduce := sorry
    preserve_stronger := sorry
  }

  instance {K ι} [Zero K] [DecidableEq K] : QReduce (FreeEq K ι) normLvl :=
  {
    reduce := λ x => if x.coef = 0 then ⟨0, 1⟩ else x
    is_reduce := sorry
    eq_reduce := sorry
    preserve_stronger := sorry
  }

  instance {K ι} [LT ι] [Zero K] : QReduce (SymEq K ι) rawLvl :=
  {
    reduce := λ x => x
    is_reduce := sorry
    eq_reduce := sorry
    preserve_stronger := sorry
  }

  instance {K ι} [LT ι] [DecidableCp ι] [Zero K] : QReduce (SymEq K ι) (redLvl 1) :=
  {
    reduce := λ x => ⟨x.coef, ⟨x.base.1.bubblesort⟩⟩
    is_reduce := sorry
    eq_reduce := sorry
    preserve_stronger := sorry
  }

  instance {K ι} [LT ι] [DecidableCp ι] [Zero K] [DecidableEq K] : QReduce (SymEq K ι) normLvl :=
  {
    reduce := λ x => if x.coef = 0 then ⟨0, 1⟩ else (QReduce.reduce (SymEq K ι) (redLvl 1) x)
    is_reduce := sorry
    eq_reduce := sorry
    preserve_stronger := sorry
  }

  instance {K ι} [LT ι] [Zero K] [Neg K] : QReduce (AltEq K ι) rawLvl :=
  {
    reduce := λ x => x
    is_reduce := sorry
    eq_reduce := sorry
    preserve_stronger := sorry
  }

  instance {K ι} [LT ι] [DecidableCp ι] [Zero K] [Neg K] : QReduce (AltEq K ι) (redLvl 1) :=
  {
    reduce := λ x =>
      let (xb, n, b) := x.base.1.bubblesortTransNum
      if b then
        ⟨0, 1⟩
      else
        let c := if n%2==0 then x.coef else -x.coef
        ⟨c, ⟨xb⟩⟩
    is_reduce := sorry
    eq_reduce := sorry
    preserve_stronger := sorry
  }

  instance {K ι} [LT ι] [DecidableCp ι] [Zero K] [Neg K] [DecidableEq K] : QReduce (AltEq K ι) normLvl :=
  {
    reduce := λ x => if x.coef = 0 then ⟨0, 1⟩ else (QReduce.reduce (AltEq K ι) (redLvl 1) x)
    is_reduce := sorry
    eq_reduce := sorry
    preserve_stronger := sorry
  }

end Monomial 
  
def FreeMonomial (K : Type v) (ι : Type u) [Zero K] := 
  Quot' (Monomial.FreeEq K ι)

def SymMonomial (K : Type v) (ι : Type u) [LT ι] [Zero K] := 
  Quot' (Monomial.SymEq K ι)

def AltMonomial (K : Type v) (ι : Type u) [LT ι] [Neg K] [Zero K]:= 
  Quot' (Monomial.AltEq K ι)

namespace FreeMonomial
  open Monomial

  variable {K ι} [Zero K] [One K] [Mul K] [DecidableEq K] -- [Reduce K] [Normalize K]  --[QNormalize (FreeEq K X)]

  instance (c : K) : IsQHom (FreeEq K ι) (FreeEq K ι) (λ x => ⟨c*x.coef, x.base⟩) := sorry
  instance (n : Nat) (c : K) : IsQHom' (redLvl n) (FreeEq K ι) (λ x => ⟨c*x.coef, x.base⟩) := sorry
  instance {n : Nat} : HMul K (FreeMonomial K ι) (FreeMonomial K ι) :=
    ⟨λ c m => Quot'.lift' (redLvl n) (λ x => ⟨c*x.coef, x.base⟩) m⟩

  instance : IsQHom₂ (FreeEq K ι) (FreeEq K ι) (FreeEq K ι) 
    (λ x y => ⟨x.coef*y.coef, x.base*y.base⟩) := sorry
  instance : Mul (FreeMonomial K ι) :=
  ⟨Quot'.lift₂ (λ x y => ⟨x.coef*y.coef, x.base*y.base⟩)⟩

  instance (c : K) : IsQHom (FreeEq K ι) (FreeEq K ι) (λ x => c * x) := sorry
  instance {n} (c : K) : IsQHom' (redLvl n) (FreeEq K ι) (λ x => c * x) := sorry
  instance : HMul K (FreeMonomial K ι) (FreeMonomial K ι) :=
  ⟨λ c => Quot'.lift' (redLvl 0) (λ x => c * x)⟩

  instance : Zero (FreeMonomial K ι) := ⟨⟦⟨⟨0, 1⟩, normLvl, sorry⟩⟧⟩
  instance : One (FreeMonomial K ι) := ⟨⟦⟨⟨1, 1⟩, normLvl, sorry⟩⟧⟩

  instance : Monomial (FreeMonomial K ι) K (FreeMonoid ι) :=
  {
    intro := λ k x => ⟦⟨⟨k, x⟩, rawLvl, sorry⟩⟧
    base := λ m => m.nrepr.base
    coef := λ m => m.nrepr.coef
  }

  instance : Semigroup (FreeMonomial K ι) :=
  {
    mul_assoc := sorry
  }

  instance : Monoid (FreeMonomial K ι) :=
  {
    mul_one := sorry
    one_mul := sorry
    npow_zero' := sorry 
    npow_succ' := sorry
  }

  instance : MonoidWithZero (FreeMonomial K ι) := 
  {
    zero_mul := sorry
    mul_zero := sorry
  }

  def toString [ToString ι] [ToString K]
    (mul smul : String) (m : FreeMonomial K ι) : String
    := 
  Id.run do
    let m' := m.nrepr
    let mut s := s!"{m'.coef}{smul}{m'.base.toString mul}"
    s

  instance [ToString ι] [ToString K] : ToString (FreeMonomial K ι) 
    := ⟨λ m => m.toString "⊗" "*"⟩

  instance {lvl} [QReduce (FreeEq K ι) lvl] : Reduce (FreeMonomial K ι) lvl := Quot'.instReduceQuot'

end FreeMonomial

namespace SymMonomial
  open Monomial

  variable {K ι} [LT ι] [DecidableCp ι] [DecidableEq K] [Zero K] [One K] [Mul K] --[Reduce K] [Normalize K] -- [QNormalize (SymEq K ι)]

  instance (c : K) : IsQHom (SymEq K ι) (SymEq K ι) (λ x => ⟨c*x.coef, x.base⟩) := sorry
  instance {n} (c : K) : IsQHom' (redLvl n) (SymEq K ι) (λ x => ⟨c*x.coef, x.base⟩) := sorry
  instance : HMul K (SymMonomial K ι) (SymMonomial K ι) :=
  ⟨λ c => Quot'.lift' (redLvl 1) (λ x => ⟨c*x.coef, x.base⟩)⟩

  instance : IsQHom₂ (SymEq K ι) (SymEq K ι) (SymEq K ι) 
    (λ x y => ⟨x.coef*y.coef, x.base*y.base⟩) := sorry
  instance : Mul (SymMonomial K ι) :=
  ⟨Quot'.lift₂ (λ x y => ⟨x.coef*y.coef, x.base*y.base⟩)⟩

  instance : Zero (SymMonomial K ι) := ⟨⟦⟨⟨0, 1⟩, normLvl, sorry⟩⟧⟩
  instance : One (SymMonomial K ι) := ⟨⟦⟨⟨1, 1⟩, normLvl, sorry⟩⟧⟩

  instance : Monomial (SymMonomial K ι) K (FreeMonoid ι) :=
  {
    intro := λ k x => ⟦⟨⟨k, x⟩, rawLvl, sorry⟩⟧
    base := λ m => m.nrepr.base
    coef := λ m => m.nrepr.coef
  }

  instance : Semigroup (SymMonomial K ι) :=
  {
    mul_assoc := sorry
  }

  instance : Monoid (SymMonomial K ι) :=
  {
    mul_one := sorry
    one_mul := sorry
    npow_zero' := sorry 
    npow_succ' := sorry
  }

  instance : MonoidWithZero (SymMonomial K ι) := 
  {
    zero_mul := sorry
    mul_zero := sorry
  }

  instance : DecidableEq (SymMonomial K ι) := 
  λ x y => if ((Monomial.coef (FreeMonoid ι) x : K) = (Monomial.coef (FreeMonoid ι) y : K)) ∧
              ((base K x : (FreeMonoid ι)) = (base K y : (FreeMonoid ι)))
           then isTrue sorry
           else isFalse sorry

  def toString [ToString ι] [ToString K] 
    (mul smul : String) (m : SymMonomial K ι) : String
    := 
  Id.run do
    let m' := m.nrepr
    if m'.coef = 1 then
      s!"{m'.base.toString mul}"
    else
      s!"{m'.coef}{smul}{m'.base.toString mul}"

  instance [ToString ι] [ToString K] : ToString (SymMonomial K ι) 
    := ⟨λ m => m.toString "*" "*"⟩

  instance {lvl} [QReduce (SymEq K ι) lvl] : Reduce (SymMonomial K ι) lvl := Quot'.instReduceQuot'

end SymMonomial

namespace AltMonomial
  open Monomial

  variable {K ι} [LT ι] [DecidableCp ι] [Zero K] [One K] [Neg K] [Mul K] [Normalize K] [DecidableEq K] -- [QNormalize (AltEq K ι)] 

  instance (c : K) : IsQHom (AltEq K ι) (AltEq K ι) (λ x => ⟨c*x.coef, x.base⟩) := sorry
  instance (n : Nat) (c : K) : IsQHom' (redLvl n) (AltEq K ι) (λ x => ⟨c*x.coef, x.base⟩) := sorry
  instance : HMul K (AltMonomial K ι) (AltMonomial K ι) :=
  ⟨
    λ c m => Quot'.lift' (redLvl 1) (λ x => ⟨c*x.coef, x.base⟩) m
  ⟩

  instance : IsQHom₂ (AltEq K ι) (AltEq K ι) (AltEq K ι) 
    (λ x y => ⟨x.coef*y.coef, x.base*y.base⟩) := sorry
  instance : Mul (AltMonomial K ι) :=
  ⟨Quot'.lift₂ (λ x y => ⟨x.coef*y.coef, x.base*y.base⟩)⟩

  instance : Zero (AltMonomial K ι) := ⟨⟦⟨⟨0, 1⟩, normLvl, sorry⟩⟧⟩
  instance : One (AltMonomial K ι) := ⟨⟦⟨⟨1, 1⟩, normLvl, sorry⟩⟧⟩

  instance : Monomial (AltMonomial K ι) K (FreeMonoid ι) :=
  {
    intro := λ k x => ⟦⟨⟨k, x⟩, rawLvl, sorry⟩⟧
    base := λ m => m.nrepr.base
    coef := λ m => m.nrepr.coef
  }

  instance : Semigroup (AltMonomial K ι) :=
  {
    mul_assoc := sorry
  }

  instance : Monoid (AltMonomial K ι) :=
  {
    mul_one := sorry
    one_mul := sorry
    npow_zero' := sorry 
    npow_succ' := sorry
  }

  instance : MonoidWithZero (AltMonomial K ι) := 
  {
    zero_mul := sorry
    mul_zero := sorry
  }

  def toString [ToString ι] [ToString K] 
    (mul smul : String) (m : AltMonomial K ι) : String
    := 
  Id.run do
    let m' := m.nrepr
    let mut s := s!"{m'.coef}{smul}{m'.base.toString mul}"
    s

  instance [ToString ι] [ToString K] : ToString (AltMonomial K ι) 
    := ⟨λ m => m.toString "∧" "*"⟩

  instance [ToString K] : ToString (AltMonomial K Nat) 
    := ⟨λ m => m.toString "∧" "*"⟩


  instance instReduce (lvl) [QReduce (AltEq K ι) lvl] : Reduce (AltMonomial K ι) lvl := Quot'.instReduceQuot'
  instance [QNormalize (AltEq K ι)] : Normalize (AltMonomial K ι) := instReduce normLvl

end AltMonomial

def m : FreeMonomial Int Nat := ⟦⟨⟨1, ⟨[0,2,0,3]⟩⟩, rawLvl, sorry⟩⟧
def p : SymMonomial Int Nat := ⟦⟨⟨2, ⟨[0,2,0,3]⟩⟩, rawLvl, sorry⟩⟧
def w : AltMonomial Int Nat := ⟦⟨⟨2, ⟨[1,0,3]⟩⟩, rawLvl, sorry⟩⟧
def w' : AltMonomial Int Nat := ⟦⟨⟨0, ⟨[5,2]⟩⟩, rawLvl, sorry⟩⟧
def w'' : AltMonomial Int Nat := ⟦⟨⟨3, ⟨[5,2]⟩⟩, rawLvl, sorry⟩⟧

example : (m |> toString) = "1*[0]⊗[2]⊗[0]⊗[3]" := by native_decide
example : (p*p |>.toDebugString) = "⟦4*[0]⊗[2]⊗[0]⊗[3]⊗[0]⊗[2]⊗[0]⊗[3]⟧₀" := by native_decide
example : (p*p |> reduce (redLvl 1) |>.toDebugString) = "⟦4*[0]⊗[0]⊗[0]⊗[0]⊗[2]⊗[2]⊗[3]⊗[3]⟧₁" := by native_decide
example : (p |> toString) = "2*[0]*[0]*[2]*[3]" := by native_decide

example : (w |> toString) = "-2*[0]∧[1]∧[3]" := by native_decide
example : (w |> reduce (redLvl 0) |>.toDebugString) = "⟦2*[1]⊗[0]⊗[3]⟧₀" := by native_decide
example : (w |> reduce (redLvl 1) |>.toDebugString) = "⟦-2*[0]⊗[1]⊗[3]⟧₁" := by native_decide
example : (w |> normalize |>.toDebugString) = "⟦-2*[0]⊗[1]⊗[3]⟧∞" := by native_decide
example : (w*w |> reduce (redLvl 1) |>.toDebugString) = "⟦0*1⟧₁" := by native_decide
example : (w*w'' |> reduce (redLvl 1) |>.toDebugString) = "⟦-6*[0]⊗[1]⊗[2]⊗[3]⊗[5]⟧₁" := by native_decide

example : (w' |> toString) = "0*1" := by native_decide
example : (w' |>.toDebugString) = "⟦0*[5]⊗[2]⟧₀" := by native_decide
example : (w' |> reduce (redLvl 1) |>.toDebugString) = "⟦0*[2]⊗[5]⟧₁" := by native_decide
example : (w' |> normalize |>.toDebugString) = "⟦0*1⟧∞" := by native_decide

example : (w*w' |>.toDebugString) = "⟦0*[1]⊗[0]⊗[3]⊗[5]⊗[2]⟧₀" := by native_decide
example : (w*w' |> reduce (redLvl 1) |>.toDebugString) = "⟦0*[0]⊗[1]⊗[2]⊗[3]⊗[5]⟧₁" := by native_decide
example : (w*w' |> normalize |>.toDebugString) = "⟦0*1⟧∞" := by native_decide

-- 𝔁₀ 𝓭𝔁₀ 𝓮₀
