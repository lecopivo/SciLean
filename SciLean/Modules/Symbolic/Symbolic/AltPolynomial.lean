import SciLean.Math.Symbolic.Basic
import SciLean.Math.Symbolic.Monomial
import SciLean.Math.Symbolic.FreeAlgebra

import SciLean.Operators.Calculus.Basic

namespace SciLean

open Symbolic

variable (ι : Type) (K : Type) [Add K] [Mul K] [One K] [Neg K]

def AltPolynomial := Quot
  (λ x y : Expr ι K =>
    (Expr.EqAlgebra x y) ∨
    (Expr.EqAntiCommutative x y))

namespace AltPolynomial 

  variable {ι : Type} {K : Type} [Add K] [Mul K] [One K] [Zero K] [Neg K]

  namespace Expr 

    open Symbolic.Expr

    def toString [ToString ι] [ToString K] (e : Expr ι K): String :=
      match e with
      | zero => "0"
      | one  => "1"
      | var i => s!"dx⟦{i}⟧"
      | neg x => s!"- {toString x}"
      | add x y => s!"({toString x} + {toString y})"
      | mul x y => s!"{toString x} ∧ {toString y}"
      | smul a x => s!"{a} {toString x}"

  end Expr

  notation " 𝓢𝓐[" ι ", " K "] " => AltPolynomial ι K
  notation " 𝓢𝓐[" ι "] "        => AltPolynomial ι ℝ

  notation " 𝓐[" V ", " K "] " => AltPolynomial (Basis.Trait.Index V) K
  notation " 𝓐[" V "] "        => AltPolynomial (Basis.Trait.Index V) ℝ

  instance : Add (AltPolynomial ι K) :=
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ FreeAlgebra.Expr.add sorry sorry x y⟩

  instance : Sub (AltPolynomial ι K) :=
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ FreeAlgebra.Expr.sub sorry sorry x y⟩

  instance : OuterMul (AltPolynomial ι K) :=
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ FreeAlgebra.Expr.mul sorry sorry x y⟩

  instance : Neg (AltPolynomial ι K) :=
    ⟨λ x => Quot.mk _ <| Quot.lift FreeAlgebra.Expr.neg sorry x⟩

  instance : HMul K (AltPolynomial ι K) (AltPolynomial ι K) :=
    ⟨λ a x => Quot.mk _ <| Quot.lift (FreeAlgebra.Expr.smul a) sorry x⟩

  instance : Zero (AltPolynomial ι K) := ⟨Quot.mk _ 0⟩
  instance : One  (AltPolynomial ι K) := ⟨Quot.mk _ 1⟩

  -- The string actually depends on the represenative element, 
  -- thus it has to be hidden behind an opaque constant
  -- The sorry here is impossible to be proven
  constant toString' [ToString ι] [ToString K] (p : AltPolynomial ι K)  : String :=
    Quot.lift (λ e : Expr ι K => Expr.toString e) sorry p

  instance [ToString ι] [ToString K] : ToString (AltPolynomial ι K) := ⟨toString'⟩

  def dx : AltPolynomial Nat Int := Quot.mk _ (Expr.var 0)
  def dy : AltPolynomial Nat Int := Quot.mk _ (Expr.var 1)

  #check dx ∧ dx


  -- #eval ((3 : Int) * dx ∧ dy + (5 : Int) * dx + dx ∧ (dx + dy)) ∧ dy

  -- def PᵣΛₖ (ι) (r k : Nat) := AntiPolynomials ι (Polynomials ι ℝ) -- polyhomials
  -- def 𝓒Λₖ (X : Type) (k : Nat) [FinEnumVec X] := AntiPolynomials (FinEnumBasis.index X) (X ⟿ ℝ)   -- smoot

  def var {ι} (i : ι) (K := ℝ) [Add K] [Mul K] [One K] : AltPolynomial ι K 
    := Quot.mk _ (Expr.var i)

  def expand {ι} [Zero K]
    [LT ι] [∀ i j : ι, Decidable (i < j)] [DecidableEq ι]
    [LT K] [∀ a b : K, Decidable (a < b)] [DecidableEq K]
    (x : AltPolynomial ι K) : AltPolynomial ι K :=
    Quot.mk _ <|
    Quot.lift 
      (λ e => e.expand)
      sorry x

  def simplify {ι} [Inhabited ι] [Inhabited K] [Zero K] [One K] [Neg K] 
    [LT ι] [∀ i j : ι, Decidable (i < j)] [DecidableEq ι]
    [LT K] [∀ a b : K, Decidable (a < b)] [DecidableEq K]
    (x : AltPolynomial ι K) : AltPolynomial ι K :=
    Quot.mk _ <| Quot.lift 
      (λ e =>
         e |> Expr.expand_to_monomials
           |> Array.map Monomial.altReduce
           |> (Array.qsort · Monomial.decLt)
           |> Monomial.together
           |> Expr.simplify
      ) sorry x

  def mapMon {ι} (f : K → AltPolynomial ι K → AltPolynomial ι K)
    (p : AltPolynomial ι K) : AltPolynomial ι K :=
    Quot.lift
      (λ e => 
         e.expand_to_monomials
         |> Array.map (λ m => f m.coeff (Quot.mk _ $ (Monomial.mk 1 m.vars).toExpr))
         |> Array.foldl (· + ·) 0
      )
      sorry p

  notation " dx⟦" i ", " K "⟧ " => AltPolynomial.var (K := K) i
  notation " dx⟦" i "⟧ " => AltPolynomial.var i

  #check mapMon (λ c x => x) (2.0 * dx⟦0⟧ + dx⟦(0 : Nat)⟧) 
  #eval  mapMon (λ c x => (Math.sqrt c : ℝ)*x) (2.0 * dx⟦0⟧ ∧ (5.0 * dx⟦0⟧) + 2.0 * dx⟦3⟧)

  def diff [Enumtype ι] (p : AltPolynomial ι K) (f : K → K) : AltPolynomial ι K := 
    p.mapMon λ a dx => ∑ i : ι, (f a) * dx

  -- #eval  dx⟦0⟧ ∧ dx⟦1⟧
  -- #check dx⟦0⟧ ∧ dx⟦1⟧

end AltPolynomial
