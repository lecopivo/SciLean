import SciLean.Tactic.IfPull

open SciLean

set_option trace.Meta.Tactic.if_pull true

#check (fun x : Float => if 1 ≤ 0 then if x ≤ 1 then 1 else 0 else 0) rewrite_by
  simp only [Tactic.if_pull]



#check (let y := 5; (if 0 < 1 then (fun x : Float => x + 2 + y) else (fun x : Float => x + 3 + y)) 42).log rewrite_by
  simp (config:={zeta:=false}) only [Tactic.if_pull]

#exit

open SciLean

set_default_scalar Float



#check ∂>! x : Float, ((x*x)*x)

#check HMul.hMul.arg_a0a1.


#check ∂! x : Float, x*x

def foo (x : Float) := ∂! (x':=x), x'*x'

#exit

def dot {n : Nat} (x y : Float^[n]) : Float := ∑ i, x[i] * y[i]

variable (a b : Int)
#check DataArrayN Float (Set.Icc a b)

open Set

#check Icc (-1) 1

def ab := ⊞ (i : Fin 10) => 1.0
def _root_.Int.toFloat (a : Int) : Float :=
  if a ≥ 0 then
    a.toNat.toFloat
  else
    -(-a).toNat.toFloat

#check (↑(Icc (-1) 1) : Type)

#check Elem
-- set_option pp.universes true in
-- set_option pp.coercions false in
-- set_option pp.all true in

def D := fun (i j : Icc (-1) 1) => (i.1.toFloat + j.1.toFloat)

#synth ArrayTypeNotation _ ((Icc (-1) 5)×Fin 10) Float
#synth IndexType ((Icc (-1) 2) × Fin 10)
#synth ArrayTypeNotation _ ((Icc (-1) 2) × Fin 10) Float

#check ⊞ (i j : Fin 10) => (1.0 : Float)
#check ⊞ (i j : Icc (-1) 1) => (1.0 : Float)

#eval dot ⊞[1.0,1.0] ⊞[1.0,1.0]
#eval dot ⊞[1.0,1.0] ⊞[1.0,1.0,1.0]

def u := ⊞[(1.0 : Float), 2.0]

#check u

#eval u[0]
#eval u[1]
#eval fun i j => (u[i],u[j])

#check ⊞[⊞[(1.0:Float), 2.0],⊞[(3.0:Float), 4.0]]

×
def A :=  ⊞[1.0, 2.0;
            3.0, 4.0]


instance : Coe Nat Float := ⟨fun i => i.toUInt64.toFloat⟩
def _root_.Fin.toFloat {n} (i : Fin n) : Float := i.1.toUInt64.toFloat

#check ⊞ (i : Fin 10) => i.toFloat

variable {n m: Nat} (x : Float^[n])

#check ⊞ i (j : Fin m) => x[i]^j.1

variable (A : Float^[(2 : Nat),(2 : Nat)])

-- #check A[0,1]
-- #check Float^[[2,2], [2,2]]  -- Fin^[4,4]

def outerProduct {n m : Nat} (x : Float^[n]) (y : Float^[m]) : Float^[n,m] :=
  ⊞ i j => x[i]*y[j]

def outerProduct' {n m : Nat} (x : Float^[n]) (y : Float^[m]) : (Float^[m])^[n] :=
  ⊞ i => (⊞ j => x[i]*y[j])
 ∑ j, A[i,j] * x[j]


variable (n : Nat)
#synth VAdd ℤ (Fin n)

instance (n : Nat) : VAdd ℤ (Fin n) := ⟨i.1 +ᵥ j⟩


def shift (


#check Float^[[-1:1]]


#check Fold.fold

#check ArrayType.max

#eval 1.0 ⊔  2.0
#check Lattice


open Scalar
def softMax {I} [IndexType I]
  (r : Float) (x : Float^I) : Float^I := Id.run do
  let m := x.max

  let mut w := 0.0
  let mut x := x

  for i in IndexType.univ I do
    let xi := exp (r*(x[i]-m))
    x[i] := xi
    w += xi

  x := (1/w) • x
  return x
  -- let x := ArrayType.map (fun xi => Scalar.exp (r*(xi-m))) x
  -- let w := ∑ i, x[i]
  -- (1/w) • x

#check ArrayType.mapMono



open Scalar

#eval DataArrayN.mapMono (⊞ (i j k : Fin 2) => (IndexType.toFin (i,j,k)).toFloat) (fun x => sqrt x)



#eval (0 : Float^[3]) |>.mapIdxMono (fun i _ => i.toFloat) |>.mapMono (fun x => sqrt x)

#eval ⊞[(1.0 :Float),2.0,3.0].fold (·+·) 0


-- n#eval (·+·)                    --

def x' := ⊞[(1.0 : Float),2.0,3.0,4.0]
def A' := ⊞ (i j : Fin 2) => (1 + 2*i.toFloat + 4*j.toFloat)

#eval ∑ i, x'[i]
#eval ∏ i, x'[i]

#eval ∑ i j, A'[i,j] eval ∏ i j, A'[i,j]







def _root_.Fin.shift {n} (i : Fin n) (j : ℤ) : Fin n :=
    { val := ((i.1 + j) % n ).toNat, isLt := sorry }




def conv1d {n k : Nat} (x : Float^[n]) (w : Float^[[-k:k]]) :=
    ⊞ (i : Fin n) => ∑ j, w[j] * x[i.shift j.1]


def conv2d {n m k : Nat} (x : Float^[n,m]) (w : Float^[[-k:k],[-k:k]]) :=
    ⊞ (i : Fin n) (j : Fin m) => ∑ a b, w[a,b] * x[i.shift a, j.shift b]


def conv2d' {n m : Nat} (k : Nat) (J : Type) {I : Type} [IndexType I] [IndexType J] [DecidableEq J]
    (w : Float^[I,J,[-k:k],[-k:k]]) (b : Float^[J,n,m]) (x : Float^[I,n,m]) : Float^[J,n,m] :=
    ⊞ κ (i : Fin n) (j : Fin m) => ∑ ι a b, w[ι,κ,a,b] * x[ι, i.shift a, j.shift b]


variable (x : Float^[3, 10,10])

#check
  fun (w₁,b₁,w₂,b₂) =>
    x |> conv2d' 3 (Fin 3) w₁ b₁
      |> conv2d' 5 (Fin 10) w₂ b₂

#check fun w b => conv2d' 3 (Fin 3) (I:=Fin 2) w

#check conv2d'

instance : VAdd ℤ (Fin n) := ⟨fun j i => i.shift j⟩


def conv1d' {n k : Nat} (x : Float^[n]) (w : Float^[[-k:k]]) :=
    ⊞ (i : Fin n) => ∑ j, w[j] *  x[j.1 +ᵥ i]


#check Float^[3, 4]
#check Float^[Fin 3, Fin 4]

#eval (-14 : ℤ) % 10
