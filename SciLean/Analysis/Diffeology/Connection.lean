import SciLean.Analysis.Diffeology.Basic


namespace SciLean


open Diffeology Util
@[ext]
structure PlotHomotopy {X : Type*} [Diffeology X] {n} (p q : (Fin n → ℝ) → X) where
  val : (Fin (n+1) → ℝ) → X
  val_is_plot : val ∈ plots (n+1)
  val_at_zero : ∀ u, val (FinAdd.mk u 0) = p u
  val_at_one  : ∀ u, val (FinAdd.mk u 1) = q u

instance {X : Type*} [Diffeology X] {n} (p q : (Fin n → ℝ) → X) :
    DFunLike (PlotHomotopy p q) (Fin 1 → ℝ) (fun _ => (Fin n → ℝ) → X) where
  coe := fun ht t x => ht.val (FinAdd.mk x t)
  coe_injective' := by
    intro p q h; ext x
    have h := congrFun h (FinAdd.snd (n:=n) (m:=1) x)
    have h := congrFun h (FinAdd.fst (n:=n) (m:=1) x)
    simp at h
    exact h


open Diffeology Util in
def PlotPointHomotopy {X : Type*} [Diffeology X] {n} (p : (Fin n → ℝ) → X) (x : X) :=
  PlotHomotopy p (fun _ => x)

instance {X : Type*} [Diffeology X] {n} (p : (Fin n → ℝ) → X) (x : X) :
    DFunLike (PlotPointHomotopy p x) (Fin 1 → ℝ) (fun _ => (Fin n → ℝ) → X) where
  coe := fun ht t x => ht.val (FinAdd.mk x t)
  coe_injective' := by
    intro p q h
    apply DFunLike.ext (F:=PlotHomotopy _ _)
    intro t; funext x
    have h := congrFun h t
    have h := congrFun h x
    simp at h
    exact h

@[simp]
theorem PlotPointHomotopy.at_zero {X : Type*} [Diffeology X] {n} (p : (Fin n → ℝ) → X) (x : X)
    (ht : PlotPointHomotopy p x) : ht 0 = p := by funext u; apply ht.val_at_zero

@[simp]
theorem PlotPointHomotopy.at_one {X : Type*} [Diffeology X] {n} (p : (Fin n → ℝ) → X) (x : X)
    (ht : PlotPointHomotopy p x) : ht 1 = fun _ => x := by funext u; apply ht.val_at_one


/-- Takes a section `v` with varying codomain and transports it along the given homotopy `ht` such
  resulting section has fixed codomain. -/
def PlotPointHomotopy.transportSection'
    {X : Type*} {E : X → Type*} [Diffeology X] [∀ x, Diffeology (E x)]
    {p : (Fin n → ℝ) → X} {x : X}
    (ht : PlotPointHomotopy p x)
    (lift : (c : (Fin 1 → ℝ) → X) → (s : Fin 1 → ℝ) → (t : Fin 1 → ℝ) → E (c s) → E (c t))
    (v : (u : (Fin n → ℝ)) → E (p u)) : (Fin n → ℝ) → E x :=
  fun u => cast (by simp) (lift (ht · u) 0 1 (cast (by simp) (v u) : E (ht 0 u)))


def PlotPointHomotopy.mk {X : Type*} [Diffeology X]
    (p : (Fin n → ℝ) → X) (hp : p ∈ plots n) (x : X) (hx : p 0 = x) : PlotPointHomotopy p x where
  val := fun ut =>
    let u := FinAdd.fst ut
    let t := FinAdd.snd ut
    p ((1-t 0)•u)
  val_is_plot := by
    apply Diffeology.smooth_comp
    · exact hp
    · fun_prop
  val_at_zero := by simp
  val_at_one := by simp[hx]


def PlotPointHomotopy.comp {n m}
    {X : Type*} [Diffeology X]
    {p : (Fin n → ℝ) → X} {x : X}
    (ht : PlotPointHomotopy p x)
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (hf : Differentiable ℝ f) :
    PlotPointHomotopy (fun u => p (f u)) x where
  val := fun ut =>
    let u := FinAdd.fst ut
    let t := FinAdd.snd ut
    ht t (f u)
  val_is_plot := by
    apply Diffeology.smooth_comp
    · exact ht.val_is_plot
    · fun_prop
  val_at_zero := by simp
  val_at_one := by simp



open Diffeology in
class Connection {X : Type*} (E : X → Type*) [Diffeology X] [∀ x, Diffeology (E x)] where
  /-- Lifts curve `c` on the base space `X` to the fibers `E (c x)` given a single fiber value `v`.

  Also known as parrallel transport of `v` along `c`. -/
  lift (c : (Fin 1 → ℝ) → X) (s t) (v : E (c s)) : E (c t)

  lift_inv (c : (Fin 1 → ℝ) → X) (hc : c ∈ plots 1) (s) (v : E (c s)) (t) :
    lift c t s (lift c s t v) = v

  lift_trans (c : (Fin 1 → ℝ) → X) (hc : c ∈ plots 1) (s r t) (v : E (c s)) :
    lift c r t (lift c s r v) = lift c s t v

  smooth_comp {n m}
    {p : (Fin n → ℝ) → Sigma E}
    {ht : PlotPointHomotopy (fun u => (p u).1) x}
    {hp₂ : ht.transportSection' lift (fun u => (p u).2) ∈ plots n}
    (f : (Fin m → ℝ) → Fin n → ℝ) (hf : Differentiable ℝ f)
    (ht' : PlotPointHomotopy (fun u => (p (f u)).1) x) :
    ht'.transportSection' lift (fun u => (p (f u)).2) ∈ plots m


def PlotPointHomotopy.transportSection
    {X : Type*} {E : X → Type*} [Diffeology X] [∀ x, Diffeology (E x)] [Connection E]
    {p : (Fin n → ℝ) → X} {x : X}
    (ht : PlotPointHomotopy p x)
    (v : (u : (Fin n → ℝ)) → E (p u)) : (Fin n → ℝ) → E x :=
  ht.transportSection' Connection.lift v

def PlotPointHomotopy.transportSection''
    {X : Type*} {E : X → Type*} [Diffeology X] [∀ x, Diffeology (E x)] [Connection E]
    {x : X}
    (v : (Fin n → ℝ) → Sigma E)
    (ht : PlotPointHomotopy (fun u => (v u).1) x) : (Fin n → ℝ) → X × E x :=
  fun u => ((v u).1, ht.transportSection' Connection.lift (fun w => (v w).2) u)


open Diffeology Util in
instance {X : Type*} (E : X → Type*) [Diffeology X] [∀ x, Diffeology (E x)] [Connection E] :
    Diffeology (Sigma E) where

  plots n c :=
    (fun u => (c u).1) ∈ plots n
    ∧
    ∀ (x : X) (ht : PlotPointHomotopy (fun u => (c u).1) x),
      ht.transportSection (fun x => (c x).2) ∈ plots n

  smooth_comp := by
    intro n m p f hp hf
    have hp₁ := hp.1
    have hp₂ := hp.2
    constructor
    · apply smooth_comp hp₁ hf
    · intro x ht
      unfold PlotPointHomotopy.transportSection
      apply Connection.smooth_comp (f:=f) (hf:=hf) -- (v := fun u => (p u).2) (f:=f) (hf:=hf)
      sorry
      sorry


  const_plot := by
    intros
    constructor
    · apply Diffeology.const_plot
    · intros
      simp
      unfold PlotPointHomotopy.transportSection
      unfold PlotPointHomotopy.transportSection'
      simp
      sorry
