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

  namespace Repr

    def toString {M K X} [ToString M] [ToString K] (x : Repr M K X) : String :=
      match x with
      | mon m => s!"{m}"
      | add x y => s!"({toString x} + {toString y})"
      | mul x y => s!"{toString x} * {toString y}"
      | lmul c x => s!"{c} * {toString x}"
    
    instance {M K X} [ToString M] [ToString K] : ToString (Repr M K X) := 
    ⟨ λ x => x.toString ⟩

    -- Reduced:
    --   - associated addition to left
    --   - eliminated scalar multiplication of monomials
    --   - multiplication of monomials
    partial def reduce {M K X} [Add K] [Mul K] [Zero K] [Monomial M K X] -- [DecidableEq M] --[Monomial M X K]
      (x : Repr M K X) : Repr M K X
      := 
      match x with
      | x * y => 
        match reduce x, reduce y with
        | mon x, mon y => mon (x*y)
        | x, lmul c y' => reduce $ (lmul c x) * y'
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
        | x, y' + y'' => reduce $ (x + y') + y''
        | x, y => x + y
      | x => x

    #check Monomial.coef

    open Monomial
    partial def reduce1 {M K X} [Add K] [Mul K] [Zero K] [Monomial M K X] 
      [DecidableEq M] [Zero M] [One M]
      [DecidableEq K] [LT X] [DecidableCp X]
      (x : Repr M K X) : Repr M K X
      :=
      match reduce x with
      | x + y => 
        match reduce1 x, reduce1 y with
        | mon x', mon y' => 
          match decCp (base K x') ((base K y') : X) with
          | cpEq h => reduce1 $ mon $ intro ((coef X x' + coef X y') : K) ((base K x') : X)
          | cpLt h => if x' = 0 then mon y' else mon x' + mon y'
          | cpGt h => if y' = 0 then mon x' else mon y' + mon x'
        | x'' + mon x', mon y' => 
          match decCp (base K x') ((base K y') : X) with
          | cpEq h => reduce1 $ x'' + (mon $ intro ((coef X x' + coef X y') : K) ((base K x') : X))
          | cpLt h => if x' = 0 then x'' + mon y' else x'' + mon x' + mon y'
          | cpGt h => reduce1 $ if y' = 0 then x'' + mon x' else x'' + mon y' + mon x'
        | x', y' => x' + y'
      | x * y =>
        match reduce1 x, reduce1 y with
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
          reduce $ lmul c (reduce1 x) 
      | x => x

  end Repr

  namespace Test

    open Quot'

    abbrev Rep := Repr (SymMonomial Int Nat) Int (FreeMonoid Nat)

    def one : Rep := Repr.mon (⟦QRepr.norm ⟨1, ⟨[]⟩⟩ sorry⟧)
    def x : Rep := Repr.mon (⟦QRepr.norm ⟨1, ⟨[0]⟩⟩ sorry⟧)
    def y : Rep := Repr.mon (⟦QRepr.norm ⟨1, ⟨[1]⟩⟩ sorry⟧)

    -- multiplication of monomials
    example : (x * (x * y) * x |>.reduce).toString = "[0]*[0]*[0]*[1]" := by nativeDecide
    example : (y * ((2:ℤ)*x) * ((3:ℤ)*x) |>.reduce |>.toString) = "6*[0]*[0]*[1]" := by nativeDecide
    -- reassociation
    example : ((x*y + ((x + y*x) + x) + y) |>.reduce |>.toString) = "(((([0]*[1] + [0]) + [0]*[1]) + [0]) + [1])" := by nativeDecide


    #eval      (x + x) |>.reduce1
    example : ((x + x) |>.reduce1 |>.toString) = "2*[0]" := by nativeDecide
    #eval      (y + x + x) |>.reduce1
    example : ((x + y + x) |>.reduce1 |>.toString) = "(2*[0] + [1])" := by nativeDecide
    #eval      x + (x + y) |>.reduce1 
    example : (x + (x + y) |>.reduce1 |>.toString) = "(2*[0] + [1])" := by nativeDecide
    #eval      x + x + y + (-1:ℤ)*x |>.reduce1 
    example : (x + x + y + (-1:ℤ)*x |>.reduce1 |>.toString) = "([0] + [1])" := by nativeDecide


    example : ((2:ℤ)*x + (3:ℤ)*x*((5:ℤ)*(x + y)) |>.reduce |>.toString) = "(2*[0] + 15*[0] * ([0] + [1]))" := by nativeDecide

    #eval x*((0:ℤ)*x + (0:ℤ)*y) |>.reduce1

    #eval (2:ℤ)*x + x*((0:ℤ)*x + (0:ℤ)*y) |>.reduce1
    example : ((2:ℤ)*x + x*((0:ℤ)*x + (0:ℤ)*y) |>.reduce1 |>.toString) = "2*[0]" := by nativeDecide

    #eval (2:ℤ)*x + x*((0:ℤ)*x + (0:ℤ)*y + one) |>.reduce1
    example : ((2:ℤ)*x + x*((0:ℤ)*x + (0:ℤ)*y + one) |>.reduce1 |>.toString) = "3*[0]" := by nativeDecide

    #eval (2:ℤ)*x + (5:ℤ)*((2:ℤ)*x + x + (0:ℤ)*y) |>.reduce1
    example : ((2:ℤ)*x + (5:ℤ)*((2:ℤ)*x + x + (0:ℤ)*y) |>.reduce1 |>.toString) = "17*[0]" := by nativeDecide

    #eval ((2:ℤ)*x + y)*((2:ℤ)*x + (1:ℤ)*y + (10:ℤ)*one + x*y) |>.reduce1

  end Test

end Algebra
