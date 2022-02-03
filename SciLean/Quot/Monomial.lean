import SciLean.Quot.FreeMonoid
import SciLean.Quot.QuotQ

partial def Nat.toSubscript (n : ℕ) : String := 
  let rec impl (k : ℕ) : String :=
    if k≠0 then
      match k%10 with
      | 0 => impl (k/10) ++ "₀"
      | 1 => impl (k/10) ++ "₁"
      | 2 => impl (k/10) ++ "₂"
      | 3 => impl (k/10) ++ "₃"
      | 4 => impl (k/10) ++ "₄"
      | 5 => impl (k/10) ++ "₅"
      | 6 => impl (k/10) ++ "₆"
      | 7 => impl (k/10) ++ "₇"
      | 8 => impl (k/10) ++ "₈"
      | 9 => impl (k/10) ++ "₉"
      | _ => ""
    else
      ""
  if n=0 then 
    "₀"
  else
    impl n

partial def Nat.toSupscript (n : ℕ) : String := 
  let rec impl (k : ℕ) : String :=
    if k≠0 then
      match k%10 with
      | 0 => impl (k/10) ++ "⁰"
      | 1 => impl (k/10) ++ "¹"
      | 2 => impl (k/10) ++ "²"
      | 3 => impl (k/10) ++ "³"
      | 4 => impl (k/10) ++ "⁴"
      | 5 => impl (k/10) ++ "⁵"
      | 6 => impl (k/10) ++ "⁶"
      | 7 => impl (k/10) ++ "⁷"
      | 8 => impl (k/10) ++ "⁸"
      | 9 => impl (k/10) ++ "⁹"
      | _ => ""
    else
      ""
  if n=0 then 
    "₀"
  else
    impl n
 
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
    RedForm := λ _ => True
    NormForm := λ x => (x.coef = 0 → x.base = 1)
    norm_red := λ x _ => True.intro
    norm_eq := sorry
  }

  instance {K ι} [LT ι] [Zero K] : QForm (SymEq K ι) :=
  {
    RedForm := λ x => x.base.1.Sorted
    NormForm := λ x => x.base.1.Sorted ∧ (x.coef = 0 → x.base = 1)
    norm_red := λ x h => h.1
    norm_eq := sorry
  }

  instance {K ι} [LT ι] [Zero K] [Neg K] : QForm (AltEq K ι) :=
  {
    RedForm := λ x => x.base.1.StrictlySorted
    NormForm := λ x => x.base.1.StrictlySorted ∧ (x.coef = 0 → x.base = 1)
    norm_red := λ x h => h.1
    norm_eq := sorry
  }

  instance {K ι} [Zero K] [Reduce K] : QReduce (FreeEq K ι) :=
  {
    reduce := λ x => ⟨reduce x.coef, x.base⟩
    is_reduce := sorry
    eq_reduce := sorry
    preserve_norm := sorry
  }

  instance {K ι} [LT ι] [DecidableCp ι] [Zero K] [Reduce K] : QReduce (SymEq K ι) :=
  {
    reduce := λ x => ⟨reduce x.coef, ⟨x.base.1.bubblesort⟩⟩
    is_reduce := sorry
    eq_reduce := sorry
    preserve_norm := sorry
  }

  -- TODO: Check for repeated element in monomial
  instance {K ι} [LT ι] [DecidableCp ι] [Zero K] [Neg K] [Reduce K] : QReduce (AltEq K ι) :=
  {
    reduce := λ x =>
      let (xb, n, b) := x.base.1.bubblesortTransNum
      if b then
        ⟨0, 1⟩
      else
        let c := reduce <| if n%2==0 then x.coef else -x.coef
        ⟨c, ⟨xb⟩⟩
    is_reduce := sorry
    eq_reduce := sorry
    preserve_norm := sorry
  }

  instance {K ι} [DecidableEq K] [Zero K] [Normalize K] : QNormalize (FreeEq K ι) :=
  {
    normalize := λ x => 
      let c := normalize x.coef
      if c = 0 then ⟨0, 1⟩ else ⟨c, x.base⟩
    is_normalize := sorry
    eq_normalize := sorry
  }

  instance {K ι} [LT ι] [DecidableCp ι] [DecidableEq K] [Zero K] [Normalize K] : QNormalize (SymEq K ι) :=
  {
    normalize := λ x => 
      let c := normalize x.coef
      let b := x.base.1.bubblesort
      if c = 0 then ⟨0, 1⟩ else ⟨c, ⟨b⟩⟩
    is_normalize := sorry
    eq_normalize := sorry
  }

  -- TODO: Check for repeated element in monomial
  instance {K ι} [LT ι] [DecidableCp ι] [DecidableEq K] [Zero K] [Neg K] [Normalize K] : QNormalize (AltEq K ι) :=
  {
    normalize := λ x => 
      let (xb, n, b) := x.base.1.bubblesortTransNum
      if b then 
        ⟨0, 1⟩
      else
        let c := normalize x.coef
        let c := if (n%2 == 0) then c else -c
        if c = 0 then ⟨0, 1⟩ else ⟨c, ⟨xb⟩⟩
    is_normalize := sorry
    eq_normalize := sorry
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

  variable {K ι} [Zero K] [One K] [Mul K] [DecidableEq K] [Reduce K] [Normalize K]  --[QNormalize (FreeEq K X)]

  instance (c : K) : IsQHom (FreeEq K ι) (FreeEq K ι) (λ x => ⟨c*x.coef, x.base⟩) := sorry
  instance (c : K) : IsQHomR (FreeEq K ι) (FreeEq K ι) (λ x => ⟨c*x.coef, x.base⟩) := sorry
  instance : HMul K (FreeMonomial K ι) (FreeMonomial K ι) :=
  ⟨
    λ c m => Quot'.rlift (λ x => ⟨c*x.coef, x.base⟩) m
  ⟩

  instance : IsQHom₂ (FreeEq K ι) (FreeEq K ι) (FreeEq K ι) 
    (λ x y => ⟨x.coef*y.coef, x.base*y.base⟩) := sorry
  instance : Mul (FreeMonomial K ι) :=
  ⟨Quot'.lift₂ (λ x y => ⟨x.coef*y.coef, x.base*y.base⟩)⟩

  instance : Monomial (FreeMonomial K ι) K (FreeMonoid ι) :=
  {
    intro := λ k x => ⟦QRepr.raw ⟨k, x⟩⟧
    base := λ m => m.nrepr.base
    coef := λ m => m.nrepr.coef
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

  instance [QReduce (FreeEq K ι)] : Reduce (FreeMonomial K ι) := Quot'.instReduceQuot'
  instance [QNormalize (FreeEq K ι)] : Normalize (FreeMonomial K ι) := Quot'.instNormalizeQuot'

end FreeMonomial

namespace SymMonomial
  open Monomial

  variable {K ι} [LT ι] [DecidableCp ι] [DecidableEq K] [Zero K] [One K] [Mul K] [Reduce K] [Normalize K] -- [QNormalize (SymEq K ι)]

  instance (c : K) : IsQHom (SymEq K ι) (SymEq K ι) (λ x => ⟨c*x.coef, x.base⟩) := sorry
  instance (c : K) : IsQHomR (SymEq K ι) (SymEq K ι) (λ x => ⟨c*x.coef, x.base⟩) := sorry
  instance : HMul K (SymMonomial K ι) (SymMonomial K ι) :=
  ⟨
    λ c m => Quot'.rlift (λ x => ⟨c*x.coef, x.base⟩) m
  ⟩

  instance : IsQHom₂ (SymEq K ι) (SymEq K ι) (SymEq K ι) 
    (λ x y => ⟨x.coef*y.coef, x.base*y.base⟩) := sorry
  instance : Mul (SymMonomial K ι) :=
  ⟨Quot'.lift₂ (λ x y => ⟨x.coef*y.coef, x.base*y.base⟩)⟩

  instance : Zero (SymMonomial K ι) := ⟨⟦QRepr.norm ⟨0, 1⟩ sorry⟧⟩
  instance : One (SymMonomial K ι) := ⟨⟦QRepr.norm ⟨1, 1⟩ sorry⟧⟩

  instance : Monomial (SymMonomial K ι) K (FreeMonoid ι) :=
  {
    intro := λ k x => ⟦QRepr.raw ⟨k, x⟩⟧
    base := λ m => m.nrepr.base
    coef := λ m => m.nrepr.coef
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

  instance [QReduce (SymEq K ι)] : Reduce (SymMonomial K ι) := Quot'.instReduceQuot'
  instance [QNormalize (SymEq K ι)] : Normalize (SymMonomial K ι) := Quot'.instNormalizeQuot'

end SymMonomial

namespace AltMonomial
  open Monomial

  variable {K ι} [LT ι] [DecidableCp ι] [Zero K] [Neg K] [Mul K] [Normalize K] [DecidableEq K] -- [QNormalize (AltEq K ι)] 

  instance (c : K) : IsQHom (AltEq K ι) (AltEq K ι) (λ x => ⟨c*x.coef, x.base⟩) := sorry
  instance (c : K) : IsQHomR (AltEq K ι) (AltEq K ι) (λ x => ⟨c*x.coef, x.base⟩) := sorry
  instance : HMul K (AltMonomial K ι) (AltMonomial K ι) :=
  ⟨
    λ c m => Quot'.rlift (λ x => ⟨c*x.coef, x.base⟩) m
  ⟩

  instance : IsQHom₂ (AltEq K ι) (AltEq K ι) (AltEq K ι) 
    (λ x y => ⟨x.coef*y.coef, x.base*y.base⟩) := sorry
  instance : Mul (AltMonomial K ι) :=
  ⟨Quot'.lift₂ (λ x y => ⟨x.coef*y.coef, x.base*y.base⟩)⟩

  instance : Monomial (AltMonomial K ι) K (FreeMonoid ι) :=
  {
    intro := λ k x =>  ⟦QRepr.raw ⟨k, x⟩⟧
    base := λ m => m.nrepr.base
    coef := λ m => m.nrepr.coef
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


  instance [QReduce (AltEq K ι)] : Reduce (AltMonomial K ι) := Quot'.instReduceQuot'
  instance [QNormalize (AltEq K ι)] : Normalize (AltMonomial K ι) := Quot'.instNormalizeQuot'

end AltMonomial

#eval ( (10 : ℕ).toSubscript)

def m : FreeMonomial Int Nat := ⟦QRepr.raw ⟨1, ⟨[0,2,0,3]⟩⟩⟧
def p : SymMonomial Int Nat := ⟦QRepr.raw ⟨1, ⟨[0,2,0,3]⟩⟩⟧
def w : AltMonomial Int Nat := ⟦QRepr.raw ⟨2, ⟨[1,0,3]⟩⟩⟧
def w' : AltMonomial Int Nat := ⟦QRepr.raw ⟨0, ⟨[5,2]⟩⟩⟧
def w'' : AltMonomial Int Nat := ⟦QRepr.raw ⟨3, ⟨[5,2]⟩⟩⟧

#check Quot'.instNormalizeQuot'.normalize

#eval m
#eval p
#eval w.toDebugString
#eval w*w''
#eval w |> Quot'.instNormalizeQuot'.normalize |>.toDebugString
#eval w |> normalize |>.toDebugString
#eval w'.toDebugString
#eval (w' |> reduce).toDebugString
#eval (w' |> normalize).toDebugString


#eval (w*w').toDebugString
#eval (w*w' |> reduce).toDebugString
#eval (w*w' |> normalize).toDebugString




-- 𝔁₀ 𝓭𝔁₀ 𝓮₀ 


