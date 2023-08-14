import SciLean.Algebra

inductive Comparison {X : Type u} [LT X] (x y : X) where
  | cpEq (h : x = y) : Comparison x y
  | cpLt (h : x < y) : Comparison x y
  | cpGt (h : x > y) : Comparison x y

export Comparison (cpEq cpLt cpGt)

class DecidableCp (X : Type u) [LT X] where
  compare (x y : X) : Comparison x y

instance [LT α] [DecidableEq α] [∀ a b : α, Decidable (a < b)] : DecidableCp α :=
{
  compare := λ x y =>
    if h : x = y 
    then cpEq h
    else if h : x < y
    then cpLt h
    else cpGt sorry
}

-- instance [LT ι] [Enumtype ι] : DecidableCp ι := sorry

instance : DecidableCp ℕ :=
{
  compare := λ x y =>
    if h : x = y 
    then cpEq h
    else if h : x < y
    then cpLt h
    else cpGt sorry
}

abbrev decCp {X} [LT X] [DecidableCp X] (x y : X) : Comparison x y := DecidableCp.compare x y

instance {X} [LT X] [DecidableCp X] : DecidableEq X := λ x y =>
  match decCp x y with
  | cpEq h => isTrue h
  | _ => isFalse sorry

instance {X} [LT X] [DecidableCp X] (x y : X) : Decidable (x < y) :=
  match decCp x y with
  | cpLt h => isTrue h
  | _ => isFalse sorry


namespace SciLean

structure FreeMonoid (X : Type u) where
  vars : List X

namespace FreeMonoid

  instance {X} : Mul (FreeMonoid X) := ⟨λ x y => ⟨x.1.append y.1⟩⟩
  instance {X} : One (FreeMonoid X) := ⟨⟨[]⟩⟩

  def rank {X} (x : FreeMonoid X) : Nat := x.1.length

  -- inductive SymmMonoidEq {X} : FreeMonoid X → FreeMonoid X → Prop where
  --   | mul_comm (x y : FreeMonoid X) : SymmMonoidEq (x*y) (y*x)

  def toString {X} [ToString X] (x : FreeMonoid X) (mul : String) : String :=
    let rec impl (l : List X) : String :=
      match l with
      | [] => "1"
      | [x1] => s!"[{x1}]"
      | x1 :: x2 :: xs => s!"[{x1}]{mul}{impl $ x2 :: xs}"
    impl x.1

  instance {X} [ToString X] : ToString (FreeMonoid X) :=
    ⟨λ x => x.toString "⊗"⟩

  def x : FreeMonoid ℕ := ⟨[0,1,2,3]⟩

  #eval x.toString " ⊗ "
  #eval x

  instance {X} : Monoid (FreeMonoid X) := 
  {
    mul_assoc := sorry
    mul_one := sorry
    one_mul := sorry
    npow_zero' := sorry
    npow_succ' := sorry
  }

-- def List.decGradedLexComparison {α}
--   [LT α] [∀ a b : α, Decidable (a < b)] [DecidableEq α]
--   (l1 l2 : List α) : Comparison
--   :=
--     match l1, l2 with
--     | x1 :: xs1, x2 :: xs2 => 
--      if x1 == x2 then
--        decGradedLexComparison xs1 xs2
--      else 
--        let n1 := xs1.length 
--        let n2 := xs2.length
--        if n1 == n2 then
--          if x1 < x2 then
--            Comparison.lt
--          else
--            Comparison.gt 
--        else if n1 < n2 then
--          Comparison.lt
--        else 
--          Comparison.gt
--      | [], x2 :: xs2 => Comparison.lt
--      | x1 :: xs1 , [] => Comparison.gt
--      | [], [] => Comparison.eq

-- open Comparison in
-- def List.decGradedLexLt {α}
--   [LT α] [∀ a b : α, Decidable (a < b)] [DecidableEq α]
--   (l1 l2 : List α) : Bool
--   :=
--   match List.decGradedLexComparison l1 l2 with
--   | eq => false
--   | lt => true
--   | gt => false

  -- Graded lexicographical ordering
  inductive lt {X : Type u} [LT X] : FreeMonoid X → FreeMonoid X → Prop where
  | rank (m m' : FreeMonoid X) (h : m.rank < m'.rank) 
    : lt m m'
  | head (m m' : FreeMonoid X) (h : m.rank = m'.rank)
         (x y : X) (h' : x < y)                       
    : lt (⟨[x]⟩*m) (⟨[y]⟩*m')
  | tail (m m' : FreeMonoid X) (x : X) (h : lt m m')
    : lt (⟨[x]⟩*m) (⟨[x]⟩*m')

  instance {X} [LT X] : LT (FreeMonoid X) := ⟨λ x y => lt x y⟩

  example : DecidableCp ℕ := by infer_instance

  def gradedLt {X} [LT X] [DecidableCp X] -- [∀ x y : X, Decidable (x < y)] [DecidableEq X] 
    (l l' : List X)
    : Ordering :=
    match decCp l.length l'.length with
    | cpLt h => Ordering.lt
    | cpGt h => Ordering.gt
    | cpEq h => 
      match l, l' with
      | x :: xs, y :: ys => 
        match decCp x y with
        | cpLt h => Ordering.lt
        | cpGt h => Ordering.gt
        | cpEq h => gradedLt xs ys
      | [], y :: ys => Ordering.lt
      | x :: xs, [] => Ordering.gt
      | [], [] => Ordering.eq

  instance {X} [LT X] [DecidableCp X] : DecidableCp (FreeMonoid X) :=
  ⟨ λ x y =>
    match gradedLt x.1 y.1 with
    | Ordering.lt => cpLt sorry
    | Ordering.gt => cpGt sorry
    | Ordering.eq => cpEq sorry⟩

    --   match m1., m'.1 with
    -- let n  := m.rank
    -- let n' := m'.rank
    -- if n < n' then
    --   cpLt sorry
    -- else if n' < n then
    --   cpGt sorry
    -- else
    --   match m.1, m'.1 with
    --   | x :: xs, y :: ys => 
    --     match compare x y with
    --     | 
    --   | [], y :: ys => cpLt sorry
    --   | x :: xs, [] => cpGt sorry
    --   | [], [] => cpEq sorry
    -- match m.1, m'.1 with
    -- | x1 :: xs1, x2 :: xs2 => 
    --  if x1 = x2 then
    --    decCp ⟨xs1⟩ ⟨xs2⟩
    --  else 
    --    let n1 := xs1.length 
    --    let n2 := xs2.length
    --    if n1 == n2 then
    --      if x1 < x2 then
    --        Comparison.lt
    --      else
    --        Comparison.gt 
    --    else if n1 < n2 then
    --      Comparison.lt
    --    else 
    --      Comparison.gt
    --  | [], x2 :: xs2 => Comparison.lt
    --  | x1 :: xs1 , [] => Comparison.gt
    --  | [], [] => Comparison.eq

end FreeMonoid

