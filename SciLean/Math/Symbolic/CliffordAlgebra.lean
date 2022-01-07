import SciLean.Math.Symbolic.Basic

--- TODO: rename `V` to `I` or `ι` as it is clear it is an index set not a module

namespace SciLean

open Symbolic

variable (V : Type) (K : Type) [Add K] [Mul K] [One K]

def ClifforAlgebra := Quot
  (λ x y : Expr V K =>
    (Expr.EqAlgebra x y))

namespace ClifforAlgebra

  variable {V : Type} {K : Type} [Add K] [Mul K] [One K] [Neg K]

  namespace Expr 

    open Symbolic.Expr

    def toString [ToString V] [ToString K] (e : Expr V K): String :=
      match e with
      | zero => "0"
      | one  => "1"
      | var v => s!"e⟦{v}⟧"
      | neg x => s!"- {toString x}"
      | add x y => s!"({toString x} + {toString y})"
      | mul x y => s!"{toString x} ⊗ {toString y}"
      | smul a x => s!"{a} {toString x}"

    -- Operations normalizing arithmetics on K and scalar multiplication
    -- However they do not apply associativity or distributivity
    -- Do we to apply associativity?
    -- Distributivity definitely not, for example we want to keep 
    -- polynomials in Horner form 1 + x * (1 + x * (1 + x)) for faster evaluation

    def add : Expr V K → Expr V K → Expr V K 
      | x, 0 => x
      | 0, y => y
      | x, y => x + y

    def sub : Expr V K → Expr V K → Expr V K 
      | x, 0 => x
      | 0, y => - y
      | x, - y => x + y
      | x, smul a y => x + (-a) * y
      | x, y => x + - y

    def mul : Expr V K → Expr V K → Expr V K 
      | 0, y => 0
      | x, 0 => 0
      | 1, y => y
      | x, 1 => x
      | smul a x, smul b y => (a*b) * (x*y)
      | smul a x, neg y => (-a) * (x*y)
      | neg x, smul b y => (-b) * (x*y)
      | neg x, neg y => x*y
      | smul a x, y => a * (x*y)
      | x, smul b y => b * (x*y)
      | neg x, y => neg (x*y)
      | x, neg y => neg (x*y)
      | x, y => x*y

    def neg : Expr V K → Expr V K
      | - 0 => 0
      | - x => x
      | smul a x => (-a) * x
      | x => - x

    -- If we add decidable equalitye we can check for a == 1
    def smul : K → Expr V K → Expr V K
      | a, 0 => 0
      | a, -x => (-a) * x
      | a, Expr.smul b x => (a*b) * x
      | a, x => a * x

  end Expr


  instance : Add (ClifforAlgebra V K) :=
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ Expr.add sorry sorry x y⟩

  instance : Sub (ClifforAlgebra V K) :=
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ Expr.sub sorry sorry x y⟩

  instance : Mul (ClifforAlgebra V K) :=
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ Expr.mul sorry sorry x y⟩

  instance : Neg (ClifforAlgebra V K) :=
    ⟨λ x => Quot.mk _ <| Quot.lift Expr.neg sorry x⟩

  instance : HMul K (ClifforAlgebra V K) (ClifforAlgebra V K) :=
    ⟨λ a x => Quot.mk _ <| Quot.lift (Expr.smul a) sorry x⟩

  instance : Zero (ClifforAlgebra V K) := ⟨Quot.mk _ 0⟩
  instance : One  (ClifforAlgebra V K) := ⟨Quot.mk _ 1⟩

  -- The string actually depends on the represenative element, thus it has to be hidden behind an opaque constant
  -- The sorry here is impossible to be proven
  constant toString [ToString V] [ToString K] (p : ClifforAlgebra V K) : String :=
    Quot.lift (λ e : Expr V K => Expr.toString e) sorry p

  instance [ToString V] [ToString K]: ToString (ClifforAlgebra V K) := ⟨toString⟩

  def toVal {R} [Ring R] (p : ClifforAlgebra V R) (vars : V → R) : R :=
    Quot.lift (λ e => e.toVal vars) sorry p

  def var {V} (v : V) (K := ℝ) [Add K] [Mul K] [One K] : ClifforAlgebra V K
    := Quot.mk _ (Expr.var v)

  def expand {ι}
    [LT ι] [∀ i j : ι, Decidable (i < j)] [DecidableEq ι]
    [LT K] [∀ a b : K, Decidable (a < b)] [DecidableEq K]
    (x : ClifforAlgebra ι K) : ClifforAlgebra ι K :=
    Quot.mk _ <|
    Quot.lift Expr.expand sorry x

  notation " 𝓕[" ι ", " K "] " => ClifforAlgebra ι K
  notation " 𝓕[" ι "] "        => ClifforAlgebra ι ℝ
  notation " 𝓣[" V "] "        => ClifforAlgebra (FinEnumBasis.index V) ℝ

  notation " e⟦" v ", " K "⟧ " => var v (K := K)
  notation " e⟦" v "⟧ "        => var v

  def x := (2 : ℝ) * e⟦0⟧ * ((3 : ℝ) * ((1: ℝ) * e⟦1⟧ + (2 : ℝ) * e⟦-3⟧))
  def y := (((e⟦0⟧ + e⟦1⟧) * e⟦0⟧ + e⟦1⟧) * e⟦2⟧)

  #eval x
  #eval x.expand
  #eval y
  #eval y.expand

end ClifforAlgebra


