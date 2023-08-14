import SciLean.Algebra
import SciLean.Quot.Monomial

namespace SciLean

namespace Algebra 

  -- M monomials  
  -- K ring
  inductive Repr (M K X : Type u) : Type u where
  | mon (m : M) : Repr M K X
  | add (x y : Repr M K X) : Repr M K X
  | mul (x y : Repr M K X) : Repr M K X
  | lmul (c : K) (x : Repr M K X) : Repr M K X
  -- | rmul (x : Repr M K) (c : K) : Repr M K

  instance {M K X} : Mul (Repr M K X) := ⟨λ x y => Repr.mul x y⟩
  instance {M K X} : Add (Repr M K X) := ⟨λ x y => Repr.add x y⟩
  instance {M K X} : HMul K (Repr M K X) (Repr M K X) := ⟨λ x y => Repr.lmul x y⟩
  -- instance {M K} : HMul (Repr M K) K (Repr M K) := ⟨λ x y => Repr.rmul x y⟩

  instance {M K X} [Zero M] : Zero (Repr M K X) := ⟨Repr.mon 0⟩
  instance {M K X} [One M]  : One (Repr M K X)  := ⟨Repr.mon 1⟩

  namespace Repr

    def toString {M K X} (s_add s_mul s_lmul : String) [ToString M] [ToString K] (x : Repr M K X) : String :=
      match x with
      | mon m => s!"{m}"
      | add x y => s!"({toString s_add s_mul s_lmul x}{s_add}{toString s_add s_mul s_lmul y})"
      | mul x y => s!"{toString s_add s_mul s_lmul x}{s_mul}{toString s_add s_mul s_lmul y}"
      | lmul c x => s!"{c}{s_lmul}{toString s_add s_mul s_lmul x}"
    
    instance {M K X} [ToString M] [ToString K] : ToString (Repr M K X) := 
    ⟨ λ x => x.toString " + " " * " " * "⟩

    def RedFormFromNot {M K X} (notForm : Repr M K X → Prop) (x : Repr M K X) : Prop :=
      match x with
      | mon x => ¬ (notForm (mon x))
      | x + y => ¬ (notForm x) ∧ ¬ (notForm y) ∧ ¬ (notForm (x + y))
      | x * y => ¬ (notForm x) ∧ ¬ (notForm y) ∧ ¬ (notForm (x * y))
      | lmul c x => ¬ (notForm x) ∧ ¬ (notForm (c * x))

    -- Rather defining reduced form we define what can't occur in reduced form
    inductive NotRed1Form {M K X} : Repr M K X → Prop where
    -- monomials should be multiplied together
    | red1_mon (m m' : M)                         : NotRed1Form ((mon m) * (mon m'))
    -- left multiplication association
    | red1_mul_assoc (x y z : Repr M K X)         : NotRed1Form (x*(y*z))
    -- scalar multiplication always on the left
    | red1_mul_lmul (x y : Repr M K X) (c : K)    : NotRed1Form (x * (c * y))
    -- no scalar multiplication on monomial
    | red1_lmul_mon (m : M) (c : K)               : NotRed1Form (c * (mon m : Repr M K X))
    -- no double scalar multiplication
    | red1_lmul_lmul (x : Repr M K X) (c c' : K)  : NotRed1Form (c * (c' * x))
    -- left addition association 
    | red1_add_assoc (x y z : Repr M K X)         : NotRed1Form (x + (y + z))

    def Red1Form {M K X} : Repr M K X → Prop := RedFormFromNot NotRed1Form

    partial def reduce1 {M K X} [Add K] [Mul K] [Zero K] [Monomial M K X] -- [DecidableEq M] --[Monomial M X K]
      (x : Repr M K X) : Repr M K X
      := 
      match x with
      | x * y => 
        match reduce1 x, reduce1 y with
        | mon x, mon y => mon (x*y)
        | x, lmul c y' => reduce1 $ (reduce1 $ lmul c x) * y'
        | x, y' * y'' => reduce1 $ x * y' * y''
        | x, y => x * y
      | lmul c x => 
        match reduce1 x with
        | mon x => mon (c*x)
        | x * y => reduce1 (c*x)*y
        | lmul d x => (c*d)*x
        | x => c * x
      | x + y =>
        match reduce1 x, reduce1 y with
        | x, y' + y'' => reduce1 $ (x + y') + y''
        | x, y => x + y
      | x => x

    @[simp]
    theorem reduce1_idempotent {M K X} [Add K] [Mul K] [Zero K] [Monomial M K X]
      (x : Repr M K X) : reduce1 (reduce1 x) = reduce1 x := sorry

    theorem reduce1_sound {M K X} [Add K] [Mul K] [Zero K] [Monomial M K X]
      (x : Repr M K X) : Red1Form (reduce1 x) := sorry

    inductive NotRed2Form {M K X} [Zero M] [LT X] [Monomial M K X] : Repr M K X → Prop where
    -- reduced2 implies reduce1
    | red2_red1 (x : Repr M K X) (h : NotRed1Form x) : NotRed2Form x
    -- addition of monomials of the same base not allowed
    | red2_mon_base (m m' : M) (h : Monomial.base K m = (Monomial.base K m' : X)) : NotRed2Form (mon m + mon m')
    -- addition of monomials has to be in correct order
    | red2_mon_order (m m' : M) (h : Monomial.base K m > (Monomial.base K m' : X)) : NotRed2Form (mon m + mon m')
    -- can't add zero
    | red2_add_zero (x : Repr M K X) : NotRed2Form (x + 0)
    -- can't add to zero
    | red2_zero_add (x : Repr M K X) : NotRed2Form (0 + x)
    -- TODO: Finish the definition
    -- | red2_add_base (x y : Repr M K X) :

    def Red2Form {M K X} [Zero M] [LT X] [Monomial M K X] : Repr M K X → Prop := RedFormFromNot NotRed2Form

    open Monomial
    partial def reduce2 {M K X} [Add K] [Mul K] [Zero K] [Monomial M K X] 
      [DecidableEq M] [Zero M] [One M]
      [DecidableEq K] [LT X] [DecidableCp X]
      (x : Repr M K X) : Repr M K X
      :=
      match reduce1 x with
      | x + y => 
        match reduce2 x, reduce2 y with
        | mon x', mon y' => 
          match decCp (base K x') ((base K y') : X) with
          | cpEq h => reduce2 $ mon $ intro ((coef X x' + coef X y') : K) ((base K x') : X)
          | cpLt h => if x' = 0 then mon y' else mon x' + mon y'
          | cpGt h => if y' = 0 then mon x' else mon y' + mon x'
        | x'' + mon x', mon y' => 
          match decCp (base K x') ((base K y') : X) with
          | cpEq h => reduce2 $ x'' + (mon $ intro ((coef X x' + coef X y') : K) ((base K x') : X))
          | cpLt h => if x' = 0 then x'' + mon y' else x'' + mon x' + mon y'
          | cpGt h => reduce2 $ if y' = 0 then x'' + mon x' else x'' + mon y' + mon x'
        | x', y' => x' + y'
      | x * y =>
        match reduce2 x, reduce2 y with
        | mon x', mon y' => mon (x'*y')
        | mon x', y' => 
          if x' = 0 
          then mon 0
          else if x' = 1 
          then y'
          else mon x' * y'
        | x', mon y' =>
          if y' = 0 
          then mon 0
          else if y' = 1 
          then x'
          else x' * mon y'
        | x', y' => x' * y'
      | lmul c x =>
        if c = 0 then
          mon 0 
        else
          reduce1 $ lmul c (reduce2 x) 
      | x => x

    @[simp]
    theorem reduce2_idempotent  {M K X} [Add K] [Mul K] [Zero K] [Monomial M K X] 
      [DecidableEq M] [Zero M] [One M]
      [DecidableEq K] [LT X] [DecidableCp X]
      (x : Repr M K X) : reduce2 (reduce2 x) = reduce2 x := sorry

    theorem reduce2_sound  {M K X} [Add K] [Mul K] [Zero K] [Monomial M K X] 
      [DecidableEq M] [Zero M] [One M]
      [DecidableEq K] [LT X] [DecidableCp X]
      (x : Repr M K X) : Red2Form (reduce2 x) := sorry

    -- Normalized form is fully expanded polynomial where terms are ordered by their degree
    inductive NotNormForm {M K X} [Zero M] [LT X] [Monomial M K X] : Repr M K X → Prop where
    -- reduced2 implies reduce1
    | norm_red2 (x : Repr M K X) (h : NotRed2Form x) : NotNormForm x
    -- addition of monomials of the same base not allowed
    | norm_mul (x y : Repr M K X) : NotNormForm (x * y)

    def NormForm {M K X} [Zero M] [LT X] [Monomial M K X] : Repr M K X → Prop := RedFormFromNot NotNormForm

    open Monomial
    partial def normalize {M K X} [Add K] [Mul K] [Zero K] [Monomial M K X] 
      [DecidableEq M] [Zero M] [One M]
      [DecidableEq K] [LT X] [DecidableCp X]
      (x : Repr M K X) : Repr M K X
      :=
    match reduce2 x with
    | x * y => 
      match normalize x, normalize y with
      | x', y' + y'' => normalize (x' * y' + x' * y'')
      | x' + x'', y' => normalize (x' * y' + x'' * y')
      | x', y' => reduce2 $ x' * y'
    -- | x * (y + z) => normalize (x * y + x * z)
    -- | (x + y) * z => normalize (x * z + y * z)
    | x + y => reduce2 $ normalize x + normalize y
    | lmul c (x + y) => normalize (c * x + c * y)
    | x => x

    @[simp]
    theorem normalize_idempotent  {M K X} [Add K] [Mul K] [Zero K] [Monomial M K X] 
      [DecidableEq M] [Zero M] [One M]
      [DecidableEq K] [LT X] [DecidableCp X]
      (x : Repr M K X) : normalize (normalize x) = normalize x := sorry

    theorem normalize_sound  {M K X} [Add K] [Mul K] [Zero K] [Monomial M K X] 
      [DecidableEq M] [Zero M] [One M]
      [DecidableEq K] [LT X] [DecidableCp X]
      (x : Repr M K X) : NormForm (normalize x) := sorry

    open Monomial in
    inductive AlgEq (M K X) [Zero M] [One M] [Add K] [LT X] [Monomial M K X] : Repr M K X → Repr M K X → Prop where
    | add_assoc (x y z : Repr M K X) : AlgEq M K X ((x + y) + z) (x + (y + z))
    | add_comm  (x y : Repr M K X) : AlgEq M K X (x + y) (y + x)
    | add_mon  (m m' : M) (h : base K m = (base K m' : X))
      : AlgEq M K X (mon m + mon m') (mon $ intro (coef X m + coef X m' : K) (base K m : X))
    | add_zero  (x : Repr M K X) : AlgEq M K X (x + 0) x

    | mul_assoc (x y z : Repr M K X) : AlgEq M K X ((x * y) * z) (x * (y * z))
    | mul_mon   (m m' : M) : AlgEq M K X (mon m * mon m') (mon (m * m'))
    | mul_zero  (x y : Repr M K X) : AlgEq M K X (1 * x) x

    | mul_add  (x y z : Repr M K X) : AlgEq M K X (x * (y + z)) (x * y + x * z)
    | lmul_add  (c : K )(x y : Repr M K X) : AlgEq M K X (c * (x + y)) (c * x + c * y)

    | lmul_mon  (c : K) (m : M) : AlgEq M K X (lmul c (mon m)) (mon (c * m))
    -- TODO: Am I missing something here?
  
    open Quot' in
    instance {M K X} [Zero M] [One M] [Add K] [LT X] [Monomial M K X] : QForm (AlgEq M K X) :=
    {
      RedForm  := λ lvl x => 
        match lvl with
        | redLvl 0 => True
        | redLvl 1 => Red1Form x
        | redLvl n => Red2Form x
        | normLvl  => NormForm x
      redform_norm := sorry
      redform_zero := sorry
      redform_succ := sorry
      redform_inf  := sorry
    }

    open Quot'

    instance {M K X} [Zero M] [One M] [Add K] [Mul K] [Zero K] [LT X] [Monomial M K X] : QReduce (AlgEq M K X) (redLvl 1) :=
    {
      reduce := λ x => x.reduce1
      is_reduce := sorry
      eq_reduce := sorry
      preserve_stronger := sorry
    }

    instance {M K X} [Add K] [Mul K] [Zero K] [Monomial M K X] 
      [DecidableEq M] [Zero M] [One M]
      [DecidableEq K] [LT X] [DecidableCp X]
      [Monomial M K X] : QReduce (AlgEq M K X) (redLvl 2) :=
    {
      reduce := λ x => x.reduce2
      is_reduce := sorry
      eq_reduce := sorry
      preserve_stronger := sorry
    }

    instance {M K X} [Add K] [Mul K] [Zero K] [Monomial M K X] 
      [DecidableEq M] [Zero M] [One M]
      [DecidableEq K] [LT X] [DecidableCp X]
      [Monomial M K X] : QReduce (AlgEq M K X) (normLvl) :=
    {
      reduce := λ x => x.normalize
      is_reduce := sorry
      eq_reduce := sorry
      preserve_stronger := sorry
    }

  end Repr

  namespace Test

    open Quot'

    abbrev Rep := Repr (SymMonomial Int Nat) Int (FreeMonoid Nat)

    def one : Rep := Repr.mon (⟦⟨⟨1, ⟨[]⟩⟩, normLvl, sorry⟩⟧)
    def x : Rep := Repr.mon (⟦⟨⟨1, ⟨[0]⟩⟩, normLvl, sorry⟩⟧)
    def y : Rep := Repr.mon (⟦⟨⟨1, ⟨[1]⟩⟩, normLvl, sorry⟩⟧)

    example : (x * (x * y) * x |>.reduce1 |> toString) = "[0]*[0]*[0]*[1]" := by native_decide
    example : (y * ((2:ℤ)*x) * ((3:ℤ)*x) |>.reduce1 |> toString) = "6*[0]*[0]*[1]" := by native_decide
    example : ((x*y + ((x + y*x) + x) + y) |>.reduce1 |> toString) = "(((([0]*[1] + [0]) + [0]*[1]) + [0]) + [1])" := by native_decide
    example : ((2:ℤ)*x + (3:ℤ)*x*((5:ℤ)*(x + y)) |>.reduce1 |> toString) = "(2*[0] + 15*[0] * ([0] + [1]))" := by native_decide

    example : ((x + x) |>.reduce2 |> toString) = "2*[0]" := by native_decide
    example : ((x + y + x) |>.reduce2 |> toString) = "(2*[0] + [1])" := by native_decide
    example : (x + (x + y) |>.reduce2 |> toString) = "(2*[0] + [1])" := by native_decide
    example : (x + x + y + (-1:ℤ)*x |>.reduce2 |> toString) = "([0] + [1])" := by native_decide
    example : ((2:ℤ)*x + x*((0:ℤ)*x + (0:ℤ)*y) |>.reduce2 |> toString) = "2*[0]" := by native_decide
    example : ((2:ℤ)*x + x*((0:ℤ)*x + (0:ℤ)*y + one) |>.reduce2 |> toString) = "3*[0]" := by native_decide
    example : ((2:ℤ)*x + (5:ℤ)*((2:ℤ)*x + x + (0:ℤ)*y) |>.reduce2 |> toString) = "17*[0]" := by native_decide
    example : (((2:ℤ)*x + y)*((2:ℤ)*x + (1:ℤ)*y + (10:ℤ)*one + x*y) |>.reduce2 |> toString) 
              = "(2*[0] + [1]) * (((10*1 + 2*[0]) + [1]) + [0]*[1])" := by native_decide

    example : ((5:ℤ)*(x + y)*((2:ℤ)*x + x + (3:ℤ)*y) |>.normalize |> toString) 
              = "((15*[0]*[0] + 30*[0]*[1]) + 15*[1]*[1])" := by native_decide
    example : (((2:ℤ)*x + y)*((2:ℤ)*x + (1:ℤ)*y + (10:ℤ)*one + x*y) |>.normalize |> toString) 
              = "((((((20*[0] + 10*[1]) + 4*[0]*[0]) + 4*[0]*[1]) + [1]*[1]) + 2*[0]*[0]*[1]) + [0]*[1]*[1])" := by native_decide
    example : ((2:ℤ)*x + (3:ℤ)*x*((5:ℤ)*(x + y)) |>.normalize |> toString) 
              = "((2*[0] + 15*[0]*[0]) + 15*[0]*[1])" := by native_decide

  end Test

end Algebra

-- Algebra that reduces to specified level
abbrev Algebra (M K X) (lvl := Quot'.redLvl 1) [MonoidWithZero M] [Ring K] [LT X] [Monomial M K X] := Quot' (Algebra.Repr.AlgEq M K X)

namespace Algebra

  open Quot'

  variable {M K X lvl} [MonoidWithZero M] [Ring K] [LT X] [Monomial M K X] [QReduce (Algebra.Repr.AlgEq M K X) lvl]

  instance : Add (Algebra M K X lvl) := ⟨λ x' y' => reduce lvl <| Quot'.lift₂ (λ x y => x + y) (hom := sorry) x' y'⟩
  instance [One K] [Neg K] : Neg (Algebra M K X lvl) := ⟨λ x' => reduce lvl <| Quot'.lift (λ x => (-1 : K)*x) (hom := sorry) x'⟩
  instance [One K] [Neg K] : Sub (Algebra M K X lvl) := ⟨λ x' y' => reduce lvl <| Quot'.lift₂ (λ x y => x + (-1 : K)*y) (hom := sorry) x' y'⟩
  instance : Mul (Algebra M K X lvl) := ⟨λ x' y' => reduce lvl <| Quot'.lift₂ (λ x y => x * y) (hom := sorry) x' y'⟩
  instance : HMul K (Algebra M K X lvl) (Algebra M K X lvl) := ⟨λ c x' => reduce lvl <| Quot'.lift (λ x => c * x) (hom := sorry) x'⟩

  instance : One (Algebra M K X lvl) := ⟨⟦⟨Repr.mon 1, normLvl, sorry⟩⟧⟩
  instance : Zero (Algebra M K X lvl) := ⟨⟦⟨Repr.mon 0, normLvl, sorry⟩⟧⟩

  -- instance (n : Nat) : OfNat (Algebra M K X lvl) n := ⟨(n : K)*(1 : Algebra M K X lvl)⟩

  -- instance : Numeric (Algebra M K X lvl) := ⟨λ n => (OfNat.ofNat n : K)*(1 : Algebra M K X lvl)⟩

  instance : AddSemigroup (Algebra M K X lvl) :=
  {
    add_assoc := sorry
  }

  instance : AddCommSemigroup (Algebra M K X lvl) :=
  {
    add_comm := sorry
  }

  instance : Semigroup (Algebra M K X lvl) :=
  {
    mul_assoc := sorry
  }

  instance : Semiring (Algebra M K X lvl) where
    add_zero := sorry
    zero_add := sorry
    nsmul_zero' := sorry
    nsmul_succ' := sorry
    zero_mul := sorry
    mul_zero := sorry
    one_mul := sorry
    mul_one := sorry
    npow_zero' := sorry
    npow_succ' := sorry

    add_comm := sorry
    left_distrib := sorry
    right_distrib := sorry

    mul_assoc := sorry

    natCast n := (n : K)*(1 : Algebra M K X lvl)
    natCast_zero := sorry
    natCast_succ := sorry

    -- mul_add := sorry
    -- add_mul := sorry
    -- ofNat_succ := sorry

  instance : Ring (Algebra M K X lvl) where
    sub_eq_add_neg := sorry
    gsmul_zero' := sorry
    gsmul_succ' := sorry
    gsmul_neg' := sorry
    add_left_neg := sorry
    
    intCast n := (n : K)*(1 : Algebra M K X lvl)
    intCast_ofNat := sorry
    intCast_negSucc := sorry

end Algebra

abbrev Polynomial (K ι) [Ring K] [DecidableEq K] [LT ι] [DecidableCp ι] 
  := Algebra (SymMonomial K ι) K (FreeMonoid ι) (lvl := Quot'.redLvl 2)

abbrev AltPolynomial (K ι) [Ring K] [DecidableEq K] [LT ι] [DecidableCp ι] 
  := Algebra (AltMonomial K ι) K (FreeMonoid ι) (lvl := Quot'.redLvl 2)

namespace Polynomial

  open Algebra.Repr
  
  open Quot'

  def x : Polynomial Int Nat := ⟦⟨mon ⟦⟨⟨1, ⟨[0]⟩⟩, normLvl, sorry⟩⟧, normLvl, sorry⟩⟧
  def xx : Polynomial Int Nat := ⟦⟨mon ⟦⟨⟨1, ⟨[0,0]⟩⟩, normLvl, sorry⟩⟧, normLvl, sorry⟩⟧
  def y : Polynomial Int Nat := ⟦⟨mon ⟦⟨⟨1, ⟨[1]⟩⟩, normLvl, sorry⟩⟧, normLvl, sorry⟩⟧

  set_option synthInstance.maxHeartbeats 5000
  #eval ((x + y + x - y + 1*x*x) * x).toDebugString

  #eval (x -y + (x + y - x) + (x + y + x - y + 1*x*x) * x) |> Quot'.normalize |>.toDebugString
  #eval (x -y + (x + y - x) + (x + y + x - y + 1*x*x) * x) |>.toDebugString

  #eval (-y + (x + y - x) + (x + y ) * x).toDebugString

end Polynomial
