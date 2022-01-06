import Mathlib

namespace SciLean

namespace Symbolic.Algebra

inductive Expr (V : Type) (K : Type) where
| zero : Expr V K
| one  : Expr V K
| var (v : V) : Expr V K
| neg (a : Expr V K) : Expr V K
| add (a b : Expr V K) : Expr V K
| mul (p q : Expr V K) : Expr V K
| smul (a : K) (p : Expr V K) : Expr V K

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

  def rank {V K} (e : Expr V K) : Nat :=
   match e with
   | zero => 0
   | one  => 0
   | var v => 1
   | neg x => rank x
   | add x y => max (rank x) (rank y)
   | mul x y => (rank x) + (rank y)
   | smul a x => rank x

  partial def expand {V K} [Mul K] [Neg K] (e : Expr V K) : Expr V K := 
    match e with
    | 0 => zero
    | 1  => one 
    | var v => var v
    | - (- x) => (expand x)
    | - (smul a x) => expand ((-a) * x)
    | - x => - (expand x)
    | x + y => 
      match (expand x), (expand y) with
      | x', y' + y'' => expand ((x' + y') + y'')
      | x', y' => x' + y'
    | x * y => 
      match (expand x), (expand y) with
      | x' + x'', y' + y'' => expand (x' * y' + x' * y'' + x'' * y' + x'' * y'')
      | x', y' + y'' => expand (x' * y' + x' * y'')
      | x' + x'', y' => expand (x' * y' + x'' * y')
      | x', y' * y'' => expand ((x' * y') * y'')
      | smul a x', smul b y' => expand ((a*b) * (x' * y'))
      | smul a x', y' => expand (a * (x' * y'))
      | x', smul a y' => expand (a * (x' * y'))
      | x', neg y' => expand $ neg $ expand (x' * y')
      | neg x', y' => expand $ neg $ expand (x' * y')
      | x', y' => x' * y'
    | smul a x => 
      match (expand x) with
      | x' + x'' => expand (a * x' + a * x'')
      | smul b x' => expand ((a*b) * x')
      | - x' => expand ((-a) * x')
      | x' => a * (expand x')

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

  -- This does not work as I would hope
  partial def reduce {V K} [Mul K] (e : Expr V K) : Expr V K := 
    match e with
    | 0 + x => reduce $ x
    | x + 0 => reduce $ x
    | 1 * x => reduce $ x
    | x * 1 => reduce $ x
    | var v => var v
    | - - x => reduce x
    | x + (y + z) => reduce $ reduce (x + y) + z
    | x * (y * z) => reduce $ reduce (x * y) * z
    | x * (y + z) => reduce $ reduce (x * y) + reduce (x * z)
    | (x + y) * z => reduce $ reduce (x * z) + reduce (y * z)
    -- | (smul a (smul b x)) => reduce $ (a*b) * reduce x
    -- | (smul a x * y) => reduce $ a * reduce (reduce x * y)
    -- | (x * smul b y) => reduce $ b * reduce (reduce x * y)
    | x + y => reduce x + reduce y
    | x * y => reduce x * reduce y
    | - x => - reduce x
    | e => e

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

  #eval (((2 : Int) * x + (3 : Int) * y + - x * (- x + y)) * ((5 : Int) * y + (7 : Int) * - x)).expand
  #eval (((2 : Int) * x + (3 : Int) * y + - z * x * (- x + y)) * ((5 : Int) * y + (7 : Int) * - x)).expand.sort_vars
  #eval (((2 : Int) * x + (3 : Int) * y + x * (x + y)) * ((5 : Int) * y + (7 : Int) * x)).reduce

end Expr

end Symbolic.Algebra

def Quot.lift_arg2 {X Y} {r : X → X → Prop} (f : X → X → Y) (h : ∀ x y y', r y y' → f x y = f x y') : X → Quot r → Y
  := (λ x => Quot.lift (f x) (h x))

def Quot.lift₂ {X Y} {r : X → X → Prop} (f : X → X → Y) 
  (h : ∀ x y y', r y y' → f x y = f x y')
  (h' : ∀ x x', r x x' → (Quot.lift_arg2 f h) x = (Quot.lift_arg2 f h) x')
  : Quot r → Quot r → Y := 
  (λ x y =>
    Quot.lift (Quot.lift_arg2 f h) h' x y)

section BasicDefinitions 
  open Symbolic.Algebra Expr

  variable (V : Type) (K : Type) [Add K] [Mul K] [One K]
  -- 
  def FreeAlgebra := Quot
    (λ x y : Expr V K =>
      (EqAlgebra x y))

  def Polynomials := Quot
    (λ x y : Expr V K =>
      (EqAlgebra x y) ∨
      (EqCommutative x y))

  def AntiPolynomials := Quot
    (λ x y : Expr V K =>
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


namespace FreeAlgebra
  variable {V : Type} {K : Type} [Add K] [Mul K] [One K]

  open Symbolic.Algebra

  instance : Add (FreeAlgebra V K) :=
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ (Expr.add) sorry sorry x y⟩

  instance : Mul (FreeAlgebra V K) :=
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ (Expr.mul) sorry sorry x y⟩

  instance : Neg (FreeAlgebra V K) :=
    ⟨λ x => Quot.mk _ <| Quot.lift (Expr.neg) sorry x⟩

  instance : HMul K (FreeAlgebra V K) (FreeAlgebra V K) :=
    ⟨λ a x => Quot.mk _ <| Quot.lift (Expr.smul a) sorry x⟩

  variable [ToString V] [ToString K]

  open Expr in
  def toString (e : Expr V K): String :=
    match e with
    | zero => "0"
    | one  => "1"
    | var v => s!"x[{v}]"
    | neg x => s!"- {toString x}"
    | add x y => s!"({toString x} + {toString y})"
    | mul x y => s!"{toString x} * {toString y}"
    | smul a x => s!"{a} {toString x}"

  -- The string actually depends on the represenative element, thus it has to be hidden behind an opaque constant
  -- The sorry here is impossible to be proven
  constant toString' (p : FreeAlgebra V K)  : String :=
    Quot.lift (λ e : Expr V K => toString e) sorry p

  instance : ToString (FreeAlgebra V K) := ⟨toString'⟩

  def toVal {R} [CommRing R] (p : FreeAlgebra V R) (vars : V → R) : R :=
    Quot.lift (λ e => e.toVal vars) sorry p

  def rank (p : FreeAlgebra V K) : Nat :=
    Quot.lift (λ e => e.rank) sorry p

end FreeAlgebra


namespace Polynomials

  variable {V : Type} {K : Type} [Add K] [Mul K] [One K]

  open Symbolic.Algebra

  instance : Add (Polynomials V K) := 
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ (Expr.add) sorry sorry x y⟩

  instance : Mul (Polynomials V K) := 
    ⟨λ x y => Quot.mk _ <| Quot.lift₂ (Expr.mul) sorry sorry x y⟩

  instance : Neg (Polynomials V K) := 
    ⟨λ x => Quot.mk _ <| Quot.lift (Expr.neg) sorry x⟩

  instance : HMul K (Polynomials V K) (Polynomials V K) := 
    ⟨λ a x => Quot.mk _ <| Quot.lift (Expr.smul a) sorry x⟩

  variable [ToString V] [ToString K] 

  open Expr in
  def toString (e : Expr V K): String :=
    match e with
    | zero => "0"
    | one  => "1"
    | var v => s!"x[{v}]"
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

  def degree (p : Polynomials V K) : Nat :=
    Quot.lift (λ e => e.rank) sorry p

end Polynomials


namespace AntiPolynomials

  variable {V : Type} {K : Type} [Add K] [Mul K] [One K]

  open Symbolic.Algebra

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
    | var v => s!"x[{v}]"
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

  def x : AntiPolynomials Nat Int := Quot.mk _ (Expr.var 0)
  def y : AntiPolynomials Nat Int := Quot.mk _ (Expr.var 1)

  #eval (3 : Int) * x ∧ y + (5 : Int) * x + x ∧ x

end AntiPolynomials


namespace TensorAlgebra

  variable {V : Type} {K : Type} [Add V] [Add K] [Mul K] [One K] [HMul K V V]

  open Symbolic.Algebra

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

  def rank (p : TensorAlgebra V K) : Nat :=
    Quot.lift (λ e => e.rank) sorry p

  def x : TensorAlgebra Int Int := Quot.mk _ (Expr.var 0)
  def y : TensorAlgebra Int Int := Quot.mk _ (Expr.var 1)

  #eval (3 : Int) * x ⊗ y + (5 : Int) * x

end TensorAlgebra


namespace ExteriorAlgebra

  variable {V : Type} {K : Type} [Add V] [Add K] [Mul K] [One K] [HMul K V V]

  open Symbolic.Algebra

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

end ExteriorAlgebra
