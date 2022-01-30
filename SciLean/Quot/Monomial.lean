import SciLean.Quot.FreeMonoid
import SciLean.Quot.QuotQ

inductive DecComparison {X : Type u} [LT X] (x y : X) where
  | cpEq (h : x = y) : DecComparison x y
  | cpLt (h : x < y) : DecComparison x y
  | cpGt (h : x > y) : DecComparison x y

export DecComparison (cpEq cpLt cpGt)

class DecCompar (X : Type u) [LT X] where
  compare (x y : X) : DecComparison x y

abbrev compare {X} [LT X] [DecCompar X] (x y : X) : DecComparison x y := DecCompar.compare x y

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


--- Sorts list and returns the number of transpositions
partial def List.bubblesortTransNum {α} [LT α] [DecCompar α] (l : List α) : List α × ℕ :=
  match l with
  | [] => ([], 0)
  | x :: xs => 
    match xs.bubblesortTransNum with
    | ([], n) => ([x], n)
    | (y :: ys, n) => 
      match compare x y with
      | cpEq h => (x :: y :: ys, n)
      | cpLt h => (x :: y :: ys, n)
      | cpGt h => 
        let (xys, n') := (x :: ys).bubblesortTransNum
        (y :: xys, n + n' + 1)

def List.bubblesort {α} [LT α] [DecCompar α] (l : List α) : List α 
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

namespace Monomial 

  structure Repr (X : Type u) (K : Type v) where
    coef : K
    base : FreeMonoid X

  instance {X K} [Mul K] [Mul X] : Mul (Repr X K) := 
    ⟨λ x y => ⟨x.coef * y.coef, x.base * y.base⟩⟩

  instance {X K} [Mul K] : HMul K (Repr X K) (Repr X K) := 
    ⟨λ a x => ⟨a * x.coef, x.base⟩⟩
  instance {X K} [Mul K] : HMul (Repr X K) K (Repr X K) := 
    ⟨λ x a => ⟨x.coef * a, x.base⟩⟩

  -- def Repr.rank {X K} (x : Repr X K) : Nat := x.base.rank

  -- Makes only multiplication on X 
  inductive Eq (X K) [Zero K] : Repr X K → Repr X K → Prop where
    | refl (x : Repr X K) : Eq X K x x
    | zero_coeff (x y : FreeMonoid X) : Eq X K ⟨0, x⟩ ⟨0, y⟩

  inductive SymEq (X K) [Zero K] : Repr X K → Repr X K → Prop where
    | eq (x y : Repr X K) (h : Eq X K x y) : SymEq X K x y
    | sym_mul (c : K) (x y : FreeMonoid X) : SymEq X K ⟨c, x * y⟩ ⟨c, y * x⟩

  inductive AltEq (X K) [Zero K] [Neg K] : Repr X K → Repr X K → Prop where
    | eq (x y : Repr X K) (h : Eq X K x y) : AltEq X K x y
    | alt_mul (c : K) (x y : FreeMonoid X) : AltEq X K ⟨c, x * y⟩ ⟨napply Neg.neg (x.rank * y.rank) c, y * x⟩

  instance {X K} [Zero K] [One X] : QForm (Eq X K) :=
  {
    RedForm := λ _ => True
    NormForm := λ x => (x.coef = 0 → x.base = 1)
    norm_red := λ x _ => True.intro
    norm_eq := sorry
  }

  instance {X K} [One X] [LT X] [Zero K] : QForm (SymEq X K) :=
  {
    RedForm := λ x => x.base.1.Sorted
    NormForm := λ x => x.base.1.Sorted ∧ (x.coef = 0 → x.base = 1)
    norm_red := λ x h => h.1
    norm_eq := sorry
  }

  instance {X K} [One X] [LT X] [Zero K] [Neg K] : QForm (AltEq X K) :=
  {
    RedForm := λ x => x.base.1.StrictlySorted
    NormForm := λ x => x.base.1.StrictlySorted ∧ (x.coef = 0 → x.base = 1)
    norm_red := λ x h => h.1
    norm_eq := sorry
  }

  instance {X K} [One X ] [Zero K] [Reduce K] : QReduce (Eq X K) :=
  {
    reduce := λ x => ⟨reduce x.coef, x.base⟩
    is_reduce := sorry
    eq_reduce := sorry
    preserve_norm := sorry
  }

  instance {X K} [One X] [LT X] [DecCompar X] [Zero K] [Reduce K] : QReduce (SymEq X K) :=
  {
    reduce := λ x => ⟨reduce x.coef, ⟨x.base.1.bubblesort⟩⟩
    is_reduce := sorry
    eq_reduce := sorry
    preserve_norm := sorry
  }

  -- TODO: Check for repeated element in monomial
  -- instance {X K} [One X] [LT X] [DecCompar X] [Zero K] [Neg K] [Reduce K] : QReduce (AltEq X K) :=
  -- {
  --   reduce := λ x => 
  --     let (b, n) := x.base.1.bubblesortTransNum
  --     let c := if n%2==0 then x.coef else -x.coef
  --     ⟨c, ⟨b⟩⟩
  --   is_reduce := sorry
  --   eq_reduce := sorry
  --   preserve_norm := sorry
  -- }

  instance {X K} [Zero K] [One X] [DecidableEq K] : QNormalize (Eq X K) :=
  {
    normalize := λ x => if x.coef = 0 then ⟨0, 1⟩ else x
    is_normalize := sorry
    eq_normalize := sorry
  }

  instance {X K} [Zero K] [One X] [LT X] [DecCompar X] [Zero K] [Normalize K] [DecidableEq K] : QNormalize (SymEq X K) :=
  {
    normalize := λ x => 
      let c := normalize x.coef
      let b := x.base.1.bubblesort
      if c = 0 then ⟨0, 1⟩ else ⟨c, ⟨b⟩⟩
    is_normalize := sorry
    eq_normalize := sorry
  }

  -- TODO: Check for repeated element in monomial
  -- instance {X K} [Zero K] [One X] [LT X] [DecCompar X] [Zero K] [Neg K] [Normalize K] [DecidableEq K] : QNormalize (AltEq X K) :=
  -- {
  --   normalize := λ x => 
  --     let (b,n) := x.base.1.bubblesortTransNum
  --     let c := normalize x.coef
  --     let c := if (n%2 == 0) then c else -c
  --     if c = 0 then ⟨0, 1⟩ else ⟨c, ⟨b⟩⟩
  --   is_normalize := sorry
  --   eq_normalize := sorry
  -- }

end Monomial 
  
abbrev Monomial (X : Type u) (K : Type v) [Monoid X] [Ring K] := 
  Quot' (Monomial.Eq X K)

abbrev SymMonomial (X : Type u) (K : Type v) [Monoid X] [LT X] [Ring K] := 
  Quot' (Monomial.SymEq X K)

abbrev AltMonomial (X : Type u) (K : Type v) [Monoid X] [LT X] [Ring K]:= 
  Quot' (Monomial.AltEq X K)

namespace Monomial

  open Monomial

  variable {X K} {S : Rel $ Repr X K} [QForm S]

  def coef [QNormalize S] (x : Quot' S) : K := x.nrepr.coef
  def base [QNormalize S] (x : Quot' S) : FreeMonoid X := x.nrepr.base

  variable (m : Monomial Nat Int)

  #check coef m
  #check base m
  #check m.repr
           

end Monomial



namespace Algebra 

  -- M monomials  
  -- K ring
  inductive Repr (M K : Type u) : Type u where
  | mon (m : M) : Repr M K
  | add (x y : Repr M K) : Repr M K
  | mul (x y : Repr M K) : Repr M K
  | lmul (c : K) (x : Repr M K) : Repr M K
  -- | rmul (x : Repr M K) (c : K) : Repr M K

  instance {M K} : Mul (Repr M K) := ⟨λ x y => Repr.mul x y⟩
  instance {M K} : Add (Repr M K) := ⟨λ x y => Repr.add x y⟩
  instance {M K} : HMul K (Repr M K) (Repr M K) := ⟨λ x y => Repr.lmul x y⟩
  -- instance {M K} : HMul (Repr M K) K (Repr M K) := ⟨λ x y => Repr.rmul x y⟩
    
  open Repr in
  partial def reduce {M K} [HMul K M M] [Mul M] [Zero M] [DecidableEq M] [Mul K] (x : Repr M K) : Repr M K
    := 
    match x with
    | x * y => 
      match reduce x, reduce y with
      | mon x, mon y => mon (x*y)
      | x, y' * y'' => reduce $ x * y' * y''
      | x, y => x * y
    | lmul c x => 
      match reduce x with
      | mon x => mon (c*x)
      | x * y => reduce (c*x)*y
      | lmul d x => (c*d)*x
      | x => c * x
    | x + y =>
      match reduce x, reduce y with
      | mon x, y => if x=0 then y else (mon x) + y
      | x, mon y => if y=0 then x else x + (mon y)
      | x, y' + y'' => reduce $ (x + y') + y''
      | x, y => x + y
    | x => x
         
    -- | x * ((mon y) * (mon z)) => reduce $ x * mon (y*z)
    -- | x * (y * z) => reduce $ (x * y) * z
    -- | x => x
    

  #check ((1 * 2) * 3)


end Algebra
