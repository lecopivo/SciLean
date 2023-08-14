import SciLean.Math.Symbolic.Basic

namespace SciLean

open Symbolic


namespace Monomial

  def toString {ι K} (m : Monomial ι K) [ToString ι] [ToString K] : String :=
    let rec run (vars : List ι) : String :=
      match vars with
        | [] => ""
        | [x] => s!"{x}"
        | x :: xs => s!"{x} * {run xs}"
    s!"{m.coeff} {run m.vars}"

  instance {ι K} [Mul K] : Mul (Monomial ι K) := 
    ⟨λ m n => ⟨m.coeff * n.coeff, m.vars.append n.vars⟩⟩

  instance {ι K} [Mul K] : HMul K (Monomial ι K) (Monomial ι K) := 
    ⟨λ a m => ⟨a * m.coeff, m.vars⟩⟩

  instance {ι K} [Mul K] : HMul (Monomial ι K) K (Monomial ι K) := 
    ⟨λ m a => ⟨m.coeff * a, m.vars⟩⟩

  instance {ι K} : HMul ι (Monomial ι K) (Monomial ι K) := 
    ⟨λ i m => ⟨m.coeff, i :: m.vars⟩⟩

  instance {ι K} : HMul (Monomial ι K) ι (Monomial ι K) := 
    ⟨λ m i => ⟨m.coeff, m.vars.append [i]⟩⟩

  -- alternating reduction
  partial def altReduce {ι K} 
  [LT ι] [∀ i j : ι, Decidable (i < j)] [DecidableEq ι]
  [Neg K] [Inhabited K] [Zero K]
  (m : Monomial ι K) : Monomial ι K := 
  let rec sort (coef : K) (vars : List ι) (isZero : Bool) [Inhabited K] : K × List ι × Bool :=
    if isZero = true then
      ⟨0, [], true⟩
    else
    match vars with
    | [] => (coef, [], false)
    | x :: xs => 
      match sort coef xs false with
      | (_, _, true) => (0, [], true)
      | (a, [], _) => (a, [x], false)
      | (a, x' :: xs', _) => 
        if x' = x then 
          sort 0 [] true -- terminate
        else if x' < x then
          let (a', xs'', is_zero) := sort a (x :: xs') false
          if is_zero then
            (0, [], true)
          else
            (- a', x' :: xs'', false)
        else
          (a, x :: x' :: xs', false)
  let (coef', vars', _) := sort m.coeff m.vars false
  ⟨coef', vars'⟩

  def together {ι K} [Add K] [One K] [Zero K] 
    [DecidableEq ι]
    (ms : Array (Monomial ι K)) : Expr ι K :=
    Id.run do
      let mut t := ms[0]
      let mut r : Expr ι K := 0
      for i in [1:ms.size] do
        if t.vars = ms[i].vars then
          t := ⟨t.coeff + ms[i].coeff, t.vars⟩
        else
          r := r + t.toExpr
          t := ms[i]
      r + t.toExpr

  #eval (Monomial.mk 1 [5,2,1,4]) |> altReduce
