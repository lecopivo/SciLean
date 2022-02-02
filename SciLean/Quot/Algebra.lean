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

  set_option trace.Meta.synthInstance true in
  partial def reduce {M K X} [Monomial M K X] [DecidableEq M] [Mul K] --[Monomial M X K]
    (x : Repr M K X) : Repr M K X
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
      | x' + mon x'', mon y => sorry
      -- | mon x, y => if x=0 then y else (mon x) + y
      -- | x, mon y => if y=0 then x else x + (mon y)
      | x, y' + y'' => reduce $ (x + y') + y''
      | x, y => x + y
    | x => x
         
  -- | x * ((mon y) * (mon z)) => reduce $ x * mon (y*z)
  -- | x * (y * z) => reduce $ (x * y) * z
  -- | x => x

  end Repr

  #check ((1 * 2) * 3)

end Algebra
