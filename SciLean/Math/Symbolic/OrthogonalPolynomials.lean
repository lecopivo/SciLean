import SciLean.Math.Symbolic.Basic


namespace SciLean.Symbolic


open Polynomials Algebra


#check (0 : Fin 1)

open Algebra in
def Polynomials.var {ι} (i : ι) : Polynomials ι ℝ := Quot.mk _ (Expr.var i)

instance {V} {K} [Add K] [Mul K] [One K] : Zero (Polynomials V K) := ⟨Quot.mk _ Expr.zero⟩
instance {V} {K} [Add K] [Mul K] [One K] : One (Polynomials V K) := ⟨Quot.mk _ Expr.one⟩

notation "x⟦" i "⟧" => Polynomials.var i

def Legendre.rec (n : Nat) : (Polynomials (Fin 1) ℝ) × (Polynomials (Fin 1) ℝ) :=
  match n with
  | 0 => (1, 0)
  | 1 => (x⟦0⟧, 1)
  | n+1 => 
    let (p, q) := rec n
    let a : ℝ := ((2 * n + 1) : ℝ) / ((n + 1) : ℝ)
    let b : ℝ := - (n : ℝ) / ((n + 1) : ℝ)
    (a * x⟦0⟧ * p + b * q, p)

def Legendre (n : Nat) := (Legendre.rec n).1

def Hermite.rec (n : Nat) : (Polynomials (Fin 1) ℝ) × (Polynomials (Fin 1) ℝ) :=
  match n with
  | 0 => (1, 0)
  | 1 => (x⟦0⟧, 1)
  | n+1 => 
    let (p, q) := rec n
    (x⟦0⟧ * p + (- n : ℝ) * q, p)

def Hermite (n : Nat) := (Hermite.rec n).1


def Hermite'.rec (n : Nat) : (Polynomials (Fin 1) ℝ) × (Polynomials (Fin 1) ℝ) :=
  match n with
  | 0 => (1, 0)
  | 1 => ((2 : ℝ) * x⟦0⟧, 1)
  | n+1 => 
    let (p, q) := rec n
    ((2 : ℝ) * x⟦0⟧ * p + (- 2 * n : ℝ) * q, p)

def Hermite' (n : Nat) := (Hermite'.rec n).1


#eval (Hermite 3)



