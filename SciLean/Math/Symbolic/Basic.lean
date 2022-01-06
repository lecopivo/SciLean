import SciLean.Categories

namespace SciLean

namespace Symbolic

inductive Expr (V : Type) (K : Type) where
| zero : Expr V K
| one  : Expr V K
| var (v : V) : Expr V K
| neg (a : Expr V K) : Expr V K
| add (a b : Expr V K) : Expr V K
| mul (p q : Expr V K) : Expr V K
| smul (a : K) (p : Expr V K) : Expr V K
-- This complicate things but allows working with polynomials with very high degree.
-- This is currently not important.
-- | pow (p : Expr V K) (n : Int) : Expr V K
-- | sub (a b : Expr' V K) : Expr' V K

structure Monomial (V K : Type) where
  coeff : K
  vars  : List V
  -- vars  : List (V × Nat) -- maybe include powers

open Expr in
def Monomial.toExpr {V K} (m : Monomial V K) : Expr V K :=
  match m.vars with
  | [] => zero
  | x :: xs => smul m.coeff $ xs.foldl (λ x v => mul x (var v)) (var x)

instance {V K} [One K] : Inhabited (Monomial V K) := ⟨1, []⟩

def Monomial.toString {V K} [ToString V] [ToString K] (m : Monomial V K) : String := 
  s!"{m.coeff} " ++ ((m.vars.map λ v => s!" x[{v}]") |> String.join)

inductive Comparison : Type where 
  | lt | eq | gt

open Comparison in
instance : ToString Comparison :=
  ⟨λ c => match c with | lt => "lt" | eq => "eq" | gt => "gt"⟩
          

def List.decGradedLexComparison {α}
  [LT α] [∀ a b : α, Decidable (a < b)] [DecidableEq α]
  (l1 l2 : List α) : Comparison
  :=
    match l1, l2 with
    | x1 :: xs1, x2 :: xs2 => 
     if x1 == x2 then
       decGradedLexComparison xs1 xs2
     else 
       let n1 := xs1.length 
       let n2 := xs2.length
       if n1 == n2 then
         if x1 < x2 then
           Comparison.lt
         else
           Comparison.gt 
       else if n1 < n2 then
         Comparison.lt
       else 
         Comparison.gt
     | [], x2 :: xs2 => Comparison.lt
     | x1 :: xs1 , [] => Comparison.gt
     | [], [] => Comparison.eq

open Comparison in
def List.decGradedLexLt {α}
  [LT α] [∀ a b : α, Decidable (a < b)] [DecidableEq α]
  (l1 l2 : List α) : Bool
  :=
  match List.decGradedLexComparison l1 l2 with
  | eq => false
  | lt => true
  | gt => false

#eval #[[1], [0,0], [0,1]].qsort List.decGradedLexLt
    
def Monomial.decComparison {V K}
  [LT V] [∀ x y : V, Decidable (x < y)] [DecidableEq V]
  [LT K] [∀ a b : K, Decidable (a < b)] [DecidableEq K]
  (m1 m2 : Monomial V K) : Comparison 
  := 
  match List.decGradedLexComparison m1.vars m2.vars with
  | Comparison.eq => 
    if m1.coeff == m2.coeff then
      Comparison.eq
    else if m1.coeff < m2.coeff then
      Comparison.lt
    else
      Comparison.gt
  | Comparison.lt => Comparison.lt
  | Comparison.gt => Comparison.gt

def Monomial.decLt {V K}
  [LT V] [∀ x y : V, Decidable (x < y)] [DecidableEq V]
  [LT K] [∀ a b : K, Decidable (a < b)] [DecidableEq K]
  (m1 m2 : Monomial V K) : Bool
  :=
  match decComparison m1 m2 with
  | Comparison.lt => true
  | _ => false

def Monomial.decEq {V K}
  [LT V] [∀ x y : V, Decidable (x < y)] [DecidableEq V]
  [LT K] [∀ a b : K, Decidable (a < b)] [DecidableEq K]
  (m1 m2 : Monomial V K) : Bool
  :=
  match decComparison m1 m2 with
  | Comparison.eq => true
  | _ => false

instance {V K} [ToString V] [ToString K] : ToString (Monomial V K) := ⟨λ m => m.toString⟩

namespace Expr

  instance {V K} : Add (Expr V K) := ⟨λ x y => add x y⟩
  instance {V K} : Mul (Expr V K) := ⟨λ x y => mul x y⟩
  instance {V K} : HMul K (Expr V K) (Expr V K) := ⟨λ a x => smul a x⟩

  instance {V K} : Neg (Expr V K) := ⟨λ x => neg x⟩

  instance {V K} : Zero (Expr V K) := ⟨zero⟩
  instance {V K} : One (Expr V K) := ⟨one⟩
  
  inductive EqAlgebra {V K} [Add K] [Mul K] [One K] : Expr V K → Expr V K → Prop where
  -- additive commutative group
  | add_assoc (p q r : Expr V K) : EqAlgebra ((p + q) + r) (p + (q + r))
  | add_comm (p q : Expr V K)    : EqAlgebra (p + q) (q + p)
  | zero_add (p : Expr V K)      : EqAlgebra (0 + p) p
  | add_neg (p : Expr V K)       : EqAlgebra (p + - p) 0
  
  -- left K Module
  | smul_add (a : K) (p q : Expr V K)  : EqAlgebra (a * (p + q)) (r * p + r * q)
  | smul_smul (a b : K) (p : Expr V K) : EqAlgebra (a * (b * p)) ((a * b) * p)
  | add_smul (a b : K) (p : Expr V K)  : EqAlgebra ((a + b) * p) (a * p + b * p)
  | one_smul (p : Expr V K)            : EqAlgebra ((1 : K) * p) p

  -- Algebra over K - i.e. (· * ·) is bilinear
  | mul_add  (p q r : Expr V K)  : EqAlgebra (r * (p + q)) (r * p + r * q)
  | add_mul  (p q r : Expr V K)  : EqAlgebra ((p + q) * r) (p * r + q * r)
  | smul_mul_smul (a b : K) (p q : Expr V K) : EqAlgebra ((a * p) * (b * q)) ((a * b) * (p * q))

  -- Associative
  | mul_assoc (p q r : Expr V K) : EqAlgebra ((p * q) * r) (p * (q * r))

  -- Unital
  | one_mul  (p : Expr V K)      : EqAlgebra (1 * p) p

  -- Free algebra is compatible with the K-module structure of V
  inductive EqAlgebraOverV {V K} [Add V] [HMul K V V] : Expr V K → Expr V K → Prop where
  | add_var (u v : V) : EqAlgebraOverV (Expr.var u + Expr.var v) (Expr.var (u + v))
  | smul_var (a : K) (u : V) : EqAlgebraOverV (a * (Expr.var (K := K) u)) (Expr.var (a * u))

  inductive EqCommutative {V K} : Expr V K → Expr V K → Prop where
  | mul_comm (p q : Expr V K) : EqCommutative (p * q) (q * p)

  inductive EqAntiCommutative {V K} : Expr V K → Expr V K → Prop where
  | mul_anti_comm (p q : Expr V K) : EqAntiCommutative (p * q) (- (q * p))

  def toVal {X V K} [Add X] [Neg X] [Mul X] [Zero X] [One X] [HMul K X X] 
    (e : Expr V K) (vars : V → X) : X :=
    match e with
    | zero => 0
    | one  => 1
    | var v => vars v
    | neg x => - (x.toVal vars)
    | add x y => (x.toVal vars) + (y.toVal vars)
    | mul x y => (x.toVal vars) * (y.toVal vars)
    | smul a x => a * (x.toVal vars)

  def min_rank {V K} (e : Expr V K) : Nat :=
    match e with
    | zero => 0
    | one  => 0
    | var v => 1
    | neg x => min_rank x
    | add x y => min (min_rank x) (min_rank y)
    | mul x y => (min_rank x) + (min_rank y)
    | smul a x => min_rank x

  def max_rank {V K} (e : Expr V K) : Nat :=
    match e with
    | zero => 0
    | one  => 0
    | var v => 1
    | neg x => max_rank x
    | add x y => max (max_rank x) (max_rank y)
    | mul x y => (max_rank x) + (max_rank y)
    | smul a x => max_rank x

  inductive is_homogenous {V K} : Nat → Expr V K → Prop where
    | one  : is_homogenous 0 one
    | zero (n) : is_homogenous n zero
    | var (v : V) : is_homogenous 1 (var v)
    | neg (x : Expr V K) (n) (h : is_homogenous n x) : is_homogenous n (- x)
    | add (x y : Expr V K) (n) (hx : is_homogenous n x) (hy : is_homogenous n y) : is_homogenous n (x + y)
    | mul (x y : Expr V K) (k l) (hx : is_homogenous k x) (hy : is_homogenous l y) : is_homogenous (k+l) (x * y)
    | smul a (x : Expr V K) (n) (h : is_homogenous n x) : is_homogenous n (a * x)

  def expand_to_monomials {V K} [One K] [Neg K] [Mul K] (e : Expr V K) : Array (Monomial V K) :=
    match e with
    | 0 => #[]
    | 1 => #[⟨1, []⟩]
    | var v => #[⟨1, [v]⟩]
    | neg x => x.expand_to_monomials.map λ m => ⟨-m.coeff, m.vars⟩
    | add x y => x.expand_to_monomials.append y.expand_to_monomials
    | mul x y => Id.run do
      let mx := x.expand_to_monomials
      let my := y.expand_to_monomials
      let mut m : Array (Monomial V K) := Array.mkEmpty (mx.size * my.size)
      for i in [0:mx.size] do
        for j in [0:my.size] do
          m := m.push ⟨mx[i].coeff * my[j].coeff, mx[i].vars.append my[j].vars⟩
      m
    | smul a x => x.expand_to_monomials.map λ m => ⟨a*m.coeff, m.vars⟩

  def expand {V K} [One K] [Neg K] [Mul K] 
    [LT V] [∀ x y : V, Decidable (x < y)] [DecidableEq V]
    [LT K] [∀ a b : K, Decidable (a < b)] [DecidableEq K]
    (e : Expr V K) : (Expr V K) 
    := 
    Id.run do
      let m := e.expand_to_monomials
      let m := m.qsort Monomial.decLt

      let mut e' : Expr V K := m[0].toExpr
      for i in [1:m.size] do
        e' := e' + m[i].toExpr
      e'

  -- partial def expand {V K} [Mul K] [Neg K] (e : Expr V K) : Expr V K := 
  --   match e with
  --   | 0 => zero
  --   | 1 => one 
  --   | var v => var v
  --   | - (- x) => (expand x)
  --   | - (smul a x) => expand ((-a) * x)
  --   | - x => - (expand x)
  --   | x + y => 
  --     match (expand x), (expand y) with
  --     | x', y' + y'' => expand ((x' + y') + y'')
  --     | x', y' => x' + y'
  --   | x * y => 
  --     match (expand x), (expand y) with
  --     | x' + x'', y' + y'' => expand (x' * y' + x' * y'' + x'' * y' + x'' * y'')
  --     | x', y' + y'' => expand (x' * y' + x' * y'')
  --     | x' + x'', y' => expand (x' * y' + x'' * y')
  --     | x', y' * y'' => expand ((x' * y') * y'')
  --     | smul a x', smul b y' => expand ((a*b) * (x' * y'))
  --     | smul a x', y' => expand (a * (x' * y'))
  --     | x', smul a y' => expand (a * (x' * y'))
  --     | x', neg y' => expand $ neg $ expand (x' * y')
  --     | neg x', y' => expand $ neg $ expand (x' * y')
  --     | x', y' => x' * y'
  --   | smul a x => 
  --     match (expand x) with
  --     | x' + x'' => expand (a * x' + a * x'')
  --     | smul b x' => expand ((a*b) * x')
  --     | - x' => expand ((-a) * x')
  --     | x' => a * (expand x')

  -- Sorts variables using bubble sort
  -- Assumes expr is already in expanded form.
  partial def sort_vars {V K} [LT V] [∀ a b : V, Decidable (a < b)] (e : Expr V K) : Expr V K :=
    match e with
    | x * var b =>
      match (sort_vars x) with
      | x' * var a => 
        if a < b 
        then x' * var a * var b
        else (sort_vars (x' * var b)) * var a
      | var a => 
        if a < b 
        then var a * var b
        else var b * var a
      | x' => x' * var b
    | x * y => sort_vars ((sort_vars x) * y)
    | - x => - sort_vars x
    | x + y => sort_vars x + sort_vars y
    | smul a x => smul a (sort_vars x)
    | x => x

  -- -- This does not work as I would hope
  -- partial def reduce {V K} [Mul K] [Neg K] (e : Expr V K) : Expr V K := 
  --   match e with
  --   | 0 + x => reduce $ x
  --   | x + 0 => reduce $ x
  --   | 1 * x => reduce $ x
  --   | x * 1 => reduce $ x
  --   | var v => var v
  --   | - - x => reduce x
  --   | x + (y + z) => reduce $ reduce (x + y) + reduce z
  --   | x * (y * z) => reduce $ reduce (x * y) * reduce z
  --   | (x + y) * z => reduce $ reduce (x * z) + reduce (y * z)
  --   | x * (y + z) => reduce $ reduce (x * y) + reduce (x * z)
  --   | smul a (smul b x) => reduce $ (a*b) * reduce x
  --   | smul a x * y => reduce $ a * reduce (x * y)
  --   | x * smul b y => reduce $ b * reduce (x * y)
  --   | smul a (x + y) => reduce $ a * reduce x + a * reduce y
  --   | smul a (-x) => reduce $ (-a) * reduce x
  --   | - smul a x => reduce $ (-a) * reduce x
  --   | (- x) * y => reduce $ - reduce (x * y)
  --   | x * (- y) => reduce $ - reduce (x * y)
  --   | x + y => reduce x + reduce y
  --   | x * y => reduce x * reduce y
  --   | smul a x => smul a (reduce x)
  --   | - x => - reduce x
  --   | e => e

  def simplify {V K} [Zero K] [DecidableEq K] (e : Expr V K) : Expr V K :=
    match e with
    | 0 * x => 0
    | x * 0 => 0
    | 1 * x => x
    | x * 1 => x
    | smul a 0 => 0
    | x + y => simplify x + simplify y
    | x * y => simplify x * simplify y
    | smul a x => if a == 0 then 0 else smul a (simplify x)
    | x => x
  

  --- expand all brackes, factor `smul` from products,  
  def algebra_norm_form {V K} (e : Expr V K) : Expr V K := sorry


  def diff {V K} (e : Expr V K) (v : V) [DecidableEq V] : Expr V K :=
    match e with
    | var v' => if v == v' then 1 else 0
    | - x => - x.diff v
    | x + y => x.diff v + y.diff v
    | x * y => x.diff v * y + x * y.diff v
    | smul a x => a * x.diff v
    | _ => 0
 
  open Expr in
  def toString {V K} [ToString V] [ToString K] (e : Expr V K): String :=
    match e with
    | zero => "0"
    | one  => "1"
    | var v => s!"x[{v}]"
    | neg x => s!"- {toString x}"
    | add x y => s!"({toString x} + {toString y})"
    | mul x y => s!"{toString x} * {toString y}"
    | smul a x => s!"{a} {toString x}"


  instance {V K} [ToString V] [ToString K] : ToString (Expr V K) := ⟨toString⟩

  def x : Expr Int Int := var 0
  def y : Expr Int Int := var 1
  def z : Expr Int Int := var 2

  #eval ((y + x * (x + y))).expand
  #eval (((2 : Int) * x + (3 : Int) * y + - x * (- x + y)) * ((5 : Int) * y + (7 : Int) * - x)).expand
  #eval (((2 : Int) * x + (3 : Int) * y + - z * x * (- x + y)) * ((5 : Int) * y + (7 : Int) * - x)).expand
  -- #eval (((2 : Int) * x + (3 : Int) * y + - z * x * (- x + y)) * ((5 : Int) * y + (7 : Int) * - x)).expand.sort_vars

  #eval ((y + x * (x + y))).expand_to_monomials
  #eval ((y + x * (x + y))).expand_to_monomials.qsort Monomial.decLt
  #eval (((2 : Int) * x + (3 : Int) * y + - x * (- x + y)) * ((5 : Int) * y + (7 : Int) * - x)).expand_to_monomials

end Expr

end Symbolic

def Quot.lift_arg2 {X Y} {r : X → X → Prop} (f : X → X → Y) (h : ∀ x y y', r y y' → f x y = f x y') : X → Quot r → Y
  := (λ x => Quot.lift (f x) (h x))

def Quot.lift₂ {X Y} {r : X → X → Prop} (f : X → X → Y) 
  (h : ∀ x y y', r y y' → f x y = f x y')
  (h' : ∀ x x', r x x' → (Quot.lift_arg2 f h) x = (Quot.lift_arg2 f h) x')
  : Quot r → Quot r → Y := 
  (λ x y =>
    Quot.lift (Quot.lift_arg2 f h) h' x y)

section BasicDefinitions 
  open Symbolic Expr

  variable (V : Type) (K : Type) [Add K] [Mul K] [One K]
  -- 
  -- def FreeAlgebra := Quot
  --   (λ x y : Expr V K =>
  --     (EqAlgebra x y))

  def Polynomials := Quot
    (λ x y : Expr V K =>
      (EqAlgebra x y) ∨
      (EqCommutative x y))

  def AntiPolynomials := Quot
    (λ x y : Expr V K =>
      (EqAlgebra x y) ∨
      (EqAntiCommutative x y))

  def Polynomial (V : Type) (K : Type) [FinEnumBasis V] [Add K] [Mul K] [One K] := Quot
    (λ x y : Expr (FinEnumBasis.index V) K =>
      (EqAlgebra x y) ∨
      (EqCommutative x y))

  def AltPolynomial (V : Type) (K : Type) [FinEnumBasis V] [Add K] [Mul K] [One K] := Quot
    (λ x y : Expr (FinEnumBasis.index V) K =>
      (EqAlgebra x y) ∨
      (EqAntiCommutative x y))

  variable [Add V] [HMul K V V]

  -- Vector space structure of V is compatible with the algebra
  def TensorAlgebra := Quot
    (λ x y : Expr V K =>
      (EqAlgebra x y) ∨
      (EqAlgebraOverV x y))

  def ExteriorAlgebra := Quot
    (λ x y : Expr V K => 
      (EqAlgebra x y) ∨ 
      (EqAlgebraOverV x y) ∨ 
      (EqAntiCommutative x y))

  class TensorMul (X : Type u) where 
    tmul : X → X → X

  class OuterMul (X : Type u) where 
    omul : X → X → X

  infixl:75 " ⊗ " => TensorMul.tmul
  infixl:75 " ∧ " => OuterMul.omul

end BasicDefinitions


namespace Polynomials


  notation " 𝓢𝓟[" V ", " K "] " => Polynomials V K
  notation " 𝓢𝓟[" V " ] "         => Polynomials V ℝ

  notation " 𝓟[" V ", " K "] " => Polynomial V K
  notation " 𝓟[" V "] "         => Polynomial V ℝ
  
  #check 𝓟[ℝ]
  #check 𝓟[ℝ×ℝ×ℝ]

  variable {V : Type} {K : Type} [Add K] [Mul K] [One K]

  open Symbolic

  instance : Add 𝓢𝓟[V, K] := 
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ (λ x' y' => x' + y') sorry sorry x y⟩

  instance : Sub 𝓢𝓟[V, K] := 
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ (λ x' y' => x' + y') sorry sorry x y⟩

  instance : Mul 𝓢𝓟[V, K] := 
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ (λ x' y' => x' * y') sorry sorry x y⟩

  instance : Neg 𝓢𝓟[V, K] := 
    ⟨λ x => Quot.mk _ <| Quot.lift (λ x' => - x') sorry x⟩

  instance : HMul K 𝓢𝓟[V, K] 𝓢𝓟[V, K] := 
    ⟨λ a x => Quot.mk _ <| Quot.lift (λ x' => a * x') sorry x⟩

  variable [ToString V] [ToString K] 

  open Expr in
  def toString (e : Expr V K): String :=
    match e with
    | zero => "0"
    | one  => "1"
    | var v => s!"x⟦{v}⟧"
    | neg x => s!"- {toString x}"
    | add x y => s!"({toString x} + {toString y})"
    | mul x y => s!"{toString x} * {toString y}"
    | smul a x => s!"{a} {toString x}"

  -- The string actually depends on the represenative element, thus it has to be hidden behind an opaque constant
  -- The sorry here is impossible to be proven
  constant toString' (p : Polynomials V K)  : String :=
    Quot.lift (λ e : Expr V K => toString e) sorry p

  instance : ToString (Polynomials V K) := ⟨toString'⟩

  def toVal {R} [CommRing R] (p : Polynomials V R) (vars : V → R) : R :=
    Quot.lift (λ e => e.toVal vars) sorry p

  instance {R} [CommRing R] : CoeFun (Polynomials (Fin 1) R) (λ _ => R → R) := ⟨λ p x => p.toVal λ _ => x⟩


  def var {ι} (i : ι) (K := ℝ) [Add K] [Mul K] [One K] : Polynomials ι K 
    := Quot.mk _ (Expr.var i)

  instance {V} {K} [Add K] [Mul K] [One K] : Zero (Polynomials V K) := ⟨Quot.mk _ Expr.zero⟩
  instance {V} {K} [Add K] [Mul K] [One K] : One (Polynomials V K) := ⟨Quot.mk _ Expr.one⟩

  notation " x⟦" i ", " K "⟧ " => Polynomials.var (K := K) i
  notation " x⟦" i "⟧ " => Polynomials.var i

  #check x⟦1⟧ * x⟦0⟧
  #eval x⟦1⟧ * x⟦0⟧

end Polynomials


namespace AntiPolynomials

  notation " 𝓢𝓐[ " V " , " K " ] " => AntiPolynomials V K
  notation " 𝓢𝓐[ " V " ] "         => AntiPolynomials V ℝ

  variable {V : Type} {K : Type} [Add K] [Mul K] [One K]

  open Symbolic

  instance : Add (AntiPolynomials V K) := 
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ (Expr.add) sorry sorry x y⟩

  instance : OuterMul (AntiPolynomials V K) := 
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ (Expr.mul) sorry sorry x y⟩

  instance : Neg (AntiPolynomials V K) := 
    ⟨λ x => Quot.mk _ <| Quot.lift (Expr.neg) sorry x⟩

  instance : HMul K (AntiPolynomials V K) (AntiPolynomials V K) := 
    ⟨λ a x => Quot.mk _ <| Quot.lift (Expr.smul a) sorry x⟩

  variable [ToString V] [ToString K] 

  open Expr in
  def toString (e : Expr V K): String :=
    match e with
    | zero => "0"
    | one  => "1"
    | var v => s!"dx⟦{v}⟧"
    | neg x => s!"- {toString x}"
    | add x y => s!"({toString x} + {toString y})"
    | mul x y => s!"{toString x} ∧ {toString y}"
    | smul a x => s!"{a} {toString x}"

  -- The string actually depends on the represenative element, thus it has to be hidden behind an opaque constant
  -- The sorry here is impossible to be proven
  constant toString' (p : AntiPolynomials V K)  : String :=
    Quot.lift (λ e : Expr V K => toString e) sorry p

  instance : ToString (AntiPolynomials V K) := ⟨toString'⟩

  -- TODO: How to do this? we have to somehow check for zero terms of the form `x ∧ x` and not count them
  def rank (p : AntiPolynomials V K) : Nat := sorry

  def dx : AntiPolynomials Nat Int := Quot.mk _ (Expr.var 0)
  def dy : AntiPolynomials Nat Int := Quot.mk _ (Expr.var 1)

  #eval ((3 : Int) * dx ∧ dy + (5 : Int) * dx + dx ∧ (dx + dy)) ∧ dy

  -- def PᵣΛₖ (ι) (r k : Nat) := AntiPolynomials ι (Polynomials ι ℝ) -- polyhomials
  -- def 𝓒Λₖ (X : Type) (k : Nat) [FinEnumVec X] := AntiPolynomials (FinEnumBasis.index X) (X ⟿ ℝ)   -- smoot

  def var {ι} (i : ι) (K := ℝ) [Add K] [Mul K] [One K] : AntiPolynomials ι K 
    := Quot.mk _ (Expr.var i)

  notation " dx⟦ " i " , " K " ⟧ " => AntiPolynomials.var (K := K) i
  notation " dx⟦ " i " ⟧ " => AntiPolynomials.var i

  #eval  dx⟦0⟧ ∧ dx⟦1⟧
  #check dx⟦0⟧ ∧ dx⟦1⟧

end AntiPolynomials


namespace TensorAlgebra

  variable {V : Type} {K : Type} [Add V] [Add K] [Mul K] [One K] [HMul K V V]

  open Symbolic

  instance : Add (TensorAlgebra V K) := 
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ (Expr.add) sorry sorry x y⟩

  instance : TensorMul (TensorAlgebra V K) := 
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ (Expr.mul) sorry sorry x y⟩

  instance : Neg (TensorAlgebra V K) := 
    ⟨λ x => Quot.mk _ <| Quot.lift (Expr.neg) sorry x⟩

  instance : HMul K (TensorAlgebra V K) (TensorAlgebra V K) := 
    ⟨λ a x => Quot.mk _ <| Quot.lift (Expr.smul a) sorry x⟩

  variable [ToString V] [ToString K] 

  open Expr in
  def toString (e : Expr V K): String :=
    match e with
    | zero => "0"
    | one  => "1"
    | var v => s!"{v}"
    | neg x => s!"- {toString x}"
    | add x y => s!"({toString x} + {toString y})"
    | mul x y => s!"{toString x} ⊗ {toString y}"
    | smul a x => s!"{a} {toString x}"

  -- The string actually depends on the represenative element, thus it has to be hidden behind an opaque constant
  -- The sorry here is impossible to be proven
  constant toString' (p : TensorAlgebra V K)  : String :=
    Quot.lift (λ e : Expr V K => toString e) sorry p

  instance : ToString (TensorAlgebra V K) := ⟨toString'⟩

  def x : TensorAlgebra Int Int := Quot.mk _ (Expr.var 0)
  def y : TensorAlgebra Int Int := Quot.mk _ (Expr.var 1)

  #eval (3 : Int) * x ⊗ y + (5 : Int) * x

end TensorAlgebra


namespace ExteriorAlgebra

  variable {V : Type} {K : Type} [Add V] [Add K] [Mul K] [One K] [HMul K V V]

  open Symbolic

  instance : Add (ExteriorAlgebra V K) := 
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ (Expr.add) sorry sorry x y⟩

  instance : OuterMul (ExteriorAlgebra V K) := 
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ (Expr.mul) sorry sorry x y⟩

  instance : Neg (ExteriorAlgebra V K) := 
    ⟨λ x => Quot.mk _ <| Quot.lift (Expr.neg) sorry x⟩

  instance : HMul K (ExteriorAlgebra V K) (ExteriorAlgebra V K) := 
    ⟨λ a x => Quot.mk _ <| Quot.lift (Expr.smul a) sorry x⟩

  variable [ToString V] [ToString K] 

  open Expr in
  def toString (e : Expr V K): String :=
    match e with
    | zero => "0"
    | one  => "1"
    | var v => s!"{v}"
    | neg x => s!"- {toString x}"
    | add x y => s!"({toString x} + {toString y})"
    | mul x y => s!"{toString x} ∧ {toString y}"
    | smul a x => s!"{a} {toString x}"

  -- The string actually depends on the represenative element, thus it has to be hidden behind an opaque constant
  -- The sorry here is impossible to be proven
  constant toString' (p : ExteriorAlgebra V K)  : String :=
    Quot.lift (λ e : Expr V K => toString e) sorry p

  instance : ToString (ExteriorAlgebra V K) := ⟨toString'⟩

  def x : ExteriorAlgebra Int Int := Quot.mk _ (Expr.var 0)
  def y : ExteriorAlgebra Int Int := Quot.mk _ (Expr.var 1)

  #eval (3 : Int) * x ∧ y + (5 : Int) * x

  -- def 𝓒Λₖ (X : Type) (k : Nat) [FinEnumVec X] := ExteriorAlgebra X (X ⟿ ℝ)   -- smoot

end ExteriorAlgebra
