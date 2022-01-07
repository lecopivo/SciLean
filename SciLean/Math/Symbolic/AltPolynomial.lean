
namespace AltPolynomial 

  notation " 𝓢𝓐[" ι ", " K "] " => AntiPolynomials ι K
  notation " 𝓢𝓐[" ι "] "        => AntiPolynomials ι ℝ

  notation " 𝓐[" V ", " K "] " => AntiPolynomials (FinEnumBasis.index V) K
  notation " 𝓐[" V "] "        => AntiPolynomials (FinEnumBasis.index V) ℝ

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
