module

public import SciLean.Math.Symbolic.Basic
public import SciLean.Math.Symbolic.Polynomial

@[expose] public section


namespace SciLean.Symbolic

open Polynomials Algebra

def Legendre.rec (n : Nat) : 𝓢𝓟[Fin 1] × 𝓢𝓟[Fin 1] :=
  match n with
  | 0 => (1, 0)
  | 1 => (x⟦0⟧, 1)
  | n+1 =>
    let (p, q) := rec n
    let a : ℝ := ((2 * n + 1) : ℝ) / ((n + 1) : ℝ)
    let b : ℝ := - (n : ℝ) / ((n + 1) : ℝ)
    (a * x⟦0⟧ * p + b * q, p)

def Legendre (n : Nat) := (Legendre.rec n).1

def Hermite.rec (n : Nat) : 𝓢𝓟[Fin 1] × 𝓢𝓟[Fin 1] :=
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
