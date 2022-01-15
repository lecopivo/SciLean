import SciLean.Math.Symbolic.Basic
import SciLean.Math.Symbolic.Monomial
import SciLean.Math.Symbolic.FreeAlgebra

namespace SciLean

open Symbolic

variable (ι : Type) (K : Type) [Add K] [Mul K] [One K] [Neg K]

def Polynomial := Quot
  (λ x y : Expr ι K =>
    (Expr.EqAlgebra x y) ∨
    (Expr.EqCommutative x y))

namespace Polynomial

  variable {ι : Type} {K : Type} [Add K] [Mul K] [One K] [Zero K] [Neg K]

  namespace Expr 

    open Symbolic.Expr

    def toString [ToString ι] [ToString K] (e : Expr ι K): String :=
      match e with
      | zero => "0"
      | one  => "1"
      | var i => s!"x⟦{i}⟧"
      | neg x => s!"- {toString x}"
      | add x y => s!"({toString x} + {toString y})"
      | mul x y => s!"{toString x} * {toString y}"
      | smul a x => s!"{a} {toString x}"

  end Expr


  notation " 𝓢𝓟[" ι ", " K "] " => Polynomial ι K
  notation " 𝓢𝓟[" ι " ] "       => Polynomial ι ℝ
  
  -- I should define FinEnumBasis over some set/ring
  -- notation " 𝓟[" V ", " K "] " => Polynomial (FinEnumBasis.index V) K
  notation " 𝓟[" V "] " => Polynomial (Basis.Trait.Index V) (Basis.Trait.Coeff V)

  instance : Add (Polynomial ι K) :=
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ FreeAlgebra.Expr.add sorry sorry x y⟩

  instance : Sub (Polynomial ι K) :=
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ FreeAlgebra.Expr.sub sorry sorry x y⟩

  instance : Mul (Polynomial ι K) :=
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ FreeAlgebra.Expr.mul sorry sorry x y⟩

  instance : Neg (Polynomial ι K) :=
    ⟨λ x => Quot.mk _ <| Quot.lift FreeAlgebra.Expr.neg sorry x⟩

  instance : HMul K (Polynomial ι K) (Polynomial ι K) :=
    ⟨λ a x => Quot.mk _ <| Quot.lift (FreeAlgebra.Expr.smul a) sorry x⟩

  instance : Zero (Polynomial ι K) := ⟨Quot.mk _ 0⟩
  instance : One  (Polynomial ι K) := ⟨Quot.mk _ 1⟩

  -- The string actually depends on the represenative element, 
  -- thus it has to be hidden behind an opaque constant
  -- The sorry here is impossible to be proven
  constant toString' [ToString ι] [ToString K] (p : Polynomial ι K)  : String :=
    Quot.lift (λ e : Expr ι K => toString e) sorry p

  instance [ToString ι] [ToString K] : ToString (Polynomial ι K) := ⟨toString'⟩

  def toVal {R} [CommRing R] (p : Polynomial ι R) (vars : ι → R) : R :=
    Quot.lift (λ e => e.toVal vars) sorry p

  instance {R} [CommRing R] : CoeFun (Polynomial (Fin 1) R) (λ _ => R → R) 
    := ⟨λ p x => p.toVal λ _ => x⟩
  -- instance {X} [FinEnumBasis X] : CoeFun (Polynomial (Basis.index X) ℝ) (λ _ => X → ℝ) 
  --   := ⟨λ p x => p.toVal λ i => FinEnumBasis.proj i x⟩

  def var {ι} (i : ι) (K := ℝ) [Add K] [Mul K] [One K] : Polynomial ι K 
    := Quot.mk _ (Expr.var i)

  def expand {ι} [Zero K]
    [LT ι] [∀ i j : ι, Decidable (i < j)] [DecidableEq ι]
    [LT K] [∀ a b : K, Decidable (a < b)] [DecidableEq K]
    (x : Polynomial ι K) : Polynomial ι K :=
    Quot.mk _ <|
    Quot.lift 
      (λ e => e.expand)
      sorry x

  def simplify {ι} [Inhabited ι]
    [LT ι] [∀ i j : ι, Decidable (i < j)] [DecidableEq ι]
    [LT K] [∀ a b : K, Decidable (a < b)] [DecidableEq K]
    (x : Polynomial ι K) : Polynomial ι K :=
    Quot.mk _ <| Quot.lift 
      (λ e =>
         e |> Expr.expand_to_monomials
           |> Array.map Monomial.symReduce
           |> (Array.qsort · Monomial.decLt)
           |> Monomial.together
           |> Expr.simplify
      ) sorry x

  notation " x⟦" i ", " K "⟧ " => Polynomial.var (K := K) i
  notation " x⟦" i "⟧ " => Polynomial.var i

  #eval x⟦1⟧ * x⟦0⟧ * ((5 : ℝ) * x⟦1⟧ * x⟦-1⟧ + 1) |> expand
  #eval x⟦1⟧ * x⟦0⟧ * ((5 : ℝ) * x⟦1⟧ * x⟦-1⟧ + 1) + x⟦0⟧ * x⟦1⟧ |> simplify

  #check 𝓟[ℝ×ℝ]

  #eval 1.4 * x⟦2⟧ * ((3.0 + 4.0) * x⟦0⟧ + x⟦0⟧) |> expand
  #eval 1.4 * x⟦2⟧ * ((3.0 + 4.0) * x⟦0⟧ + x⟦0⟧) |> simplify

end Polynomial
