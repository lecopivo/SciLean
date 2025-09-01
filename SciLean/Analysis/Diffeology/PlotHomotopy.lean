import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.TangentSpace
import SciLean.Analysis.Diffeology.TangentBundle

namespace SciLean


local notation:max "ℝ^" n:max => (Fin n) → ℝ


open Diffeology Util
/-- Homotopy between two n-plots `p` and `q` which is itself (n+1)-plot. -/
@[ext]
structure PlotHomotopy {X : Type*} [Diffeology X] {n} (p q : ℝ^n → X) where
  val : ℝ^(n+1) → X
  val_is_plot : val ∈ plots (n+1)
  val_at_zero : ∀ u, val (FinAdd.mk u 0) = p u
  val_at_one  : ∀ u, val (FinAdd.mk u 1) = q u

instance {X : Type*} [Diffeology X] {n} (p q : ℝ^n → X) :
    DFunLike (PlotHomotopy p q) ℝ^1 (fun _ => ℝ^n → X) where
  coe := fun ht t x => ht.val (FinAdd.mk x t)
  coe_injective' := by
    intro p q h; ext x
    have h := congrFun h (FinAdd.snd (n:=n) (m:=1) x)
    have h := congrFun h (FinAdd.fst (n:=n) (m:=1) x)
    simp at h
    exact h


@[simp]
theorem PlotHomotopy.at_zero {X : Type*} [Diffeology X] {n} (p q : ℝ^n → X)
    (ht : PlotHomotopy p q) : ht 0 = p := by funext u; apply ht.val_at_zero

@[simp]
theorem PlotHomotopy.at_zero' {X : Type*} [Diffeology X] {n} (p q : ℝ^n → X)
    (ht : PlotHomotopy p q) : ht (fun _ => 0) = p := by funext u; apply ht.val_at_zero

@[simp]
theorem PlotHomotopy.at_one {X : Type*} [Diffeology X] {n} (p q: (Fin n → ℝ) → X)
    (ht : PlotHomotopy p q) : ht 1 = q := by funext u; apply ht.val_at_one

@[simp]
theorem PlotHomotopy.at_one' {X : Type*} [Diffeology X] {n} (p q: (Fin n → ℝ) → X)
    (ht : PlotHomotopy p q) : ht (fun _ => 1) = q := by funext u; apply ht.val_at_one

/-- Smooth transition from `0` to `1` on `[0,∞)`  -/
noncomputable
def smoothTransition (x : ℝ) : ℝ :=
  if x > 0 then
     Real.exp (-1/x)
  else
     0

/-- Smooth transition from `0` to `1` on `[0,1]`  -/
noncomputable
def smoothStep (x : ℝ) : ℝ :=
  smoothTransition x / (smoothTransition x + smoothTransition (1 - x))

@[simp]
theorem smoothStep_zero : smoothStep 0 = 0 := by simp[smoothStep,smoothTransition]

@[simp]
theorem smoothStep_one : smoothStep 1 = 1 := by simp[smoothStep,smoothTransition]

/-- Compose two homotopies `p ~ q` and `q ~ r` and return `p ~ r`. -/
noncomputable
def PlotHomotopy.comp {n}
    {X : Type*} [Diffeology X]
    {p q r : ℝ^n → X}
    (f : PlotHomotopy q r) (g : PlotHomotopy p q) : PlotHomotopy p r where

  val := fun ut =>
    let u := FinAdd.fst ut
    let t := FinAdd.snd ut 0
    if t < 1/3 then
      let t' := fun _ => smoothStep (3*t)
      g t' u
    else if t < 2/3 then
      r u
    else
      let t' := fun _ => smoothStep (3*t-2)
      f t' u

  val_is_plot := sorry -- This is currently unprovable as diffeology is missing "Locality axiom"
  val_at_zero := by simp
  val_at_one := by norm_num


noncomputable
def PlotHomotopy.vcomp {n}
    {X : Type*} [Diffeology X]
    {p q : ℝ^n → X}
    (f : PlotHomotopy p q) (g : ℝ^m → ℝ^n) (hg : ContDiff ℝ ⊤ g) : PlotHomotopy (p∘g) (q∘g) where

  val := fun ut =>
    let u := FinAdd.fst ut
    let t := FinAdd.snd ut
    f t (g u)

  val_is_plot := plot_comp f.val_is_plot (by fun_prop)
  val_at_zero := by simp
  val_at_one := by simp



/-- Compose two point homotopies `x ~ y` and `y ~ z` into homotopy `x ~ z`.
This can be done irrespective of the dimension of the plots as we   -/
noncomputable
def PlotHomotopy.pathComp {n m}
    {X : Type*} [Diffeology X] {x y z : X}
    (f : PlotHomotopy (fun _ : ℝ^m => y) (fun _ : ℝ^m => z))
    (g : PlotHomotopy (fun _ : ℝ^n => x) (fun _ : ℝ^n => y))
    (k : ℕ) : PlotHomotopy (fun _ : ℝ^k => x) (fun _ : ℝ^k => z) where

  val := fun ut =>
    let u := FinAdd.fst ut
    let t := FinAdd.snd ut 0
    if t < 1/3 then
      let t' := fun _ => smoothStep (3*t)
      g t' 0
    else if t < 2/3 then
      y
    else
      let t' := fun _ => smoothStep (3*t-2)
      f t' 0

  val_is_plot := sorry -- This is currently unprovable as diffeology is missing "Locality axiom"
  val_at_zero := by simp
  val_at_one := by norm_num


def PlotHomotopy.reverse {n}
    {X : Type*} [Diffeology X]
    {p q : ℝ^n → X} (f : PlotHomotopy p q) : PlotHomotopy q p where

  val := fun ut =>
    let u := FinAdd.fst ut
    let t := FinAdd.snd ut
    f (1-t) u
  val_is_plot := plot_comp (f.val_is_plot) (by fun_prop)
  val_at_zero := by simp
  val_at_one := by simp


def PlotHomotopy.toPoint {n}
    {X : Type*} [Diffeology X]
    (p : ℝ^n → X) (hp : p ∈ plots n) (v : ℝ^n) : PlotHomotopy p (fun _ => p v) where

  val := fun ut =>
    let u := FinAdd.fst ut
    let t := FinAdd.snd ut
    p ((1-t 0)•(u-v)+v)
  val_is_plot := plot_comp hp (by fun_prop)
  val_at_zero := by simp
  val_at_one := by simp


def PlotHomotopy.fromPoint {n}
    {X : Type*} [Diffeology X]
    (v : ℝ^n) (p : ℝ^n → X) (hp : p ∈ plots n) : PlotHomotopy (fun _ => p v) p where

  val := fun ut =>
    let u := FinAdd.fst ut
    let t := FinAdd.snd ut
    p (t 0•(u-v)+v)
  val_is_plot := plot_comp hp (by fun_prop)
  val_at_zero := by simp
  val_at_one := by simp


def PlotHomotopy.end_plot {n}
    {X : Type*} [Diffeology X] {p q: ℝ^n → X}
    (f : PlotHomotopy p q) : q ∈ plots n := sorry


def PlotHomotopy.start_plot {n}
    {X : Type*} [Diffeology X] {p q: ℝ^n → X}
    (f : PlotHomotopy p q) : q ∈ plots n := sorry

def PlotHomotopy.toPathAt {n}
    {X : Type*} [Diffeology X] {p q : ℝ^n → X}
    (f : PlotHomotopy p q) (u : ℝ^n) :
    PlotHomotopy (fun _ : ℝ^0 => p u) (fun _ => q u) where

  val := fun ut =>
    let t := FinAdd.snd ut
    f t u
  val_is_plot := plot_comp f.val_is_plot (by fun_prop)
  val_at_zero := by simp
  val_at_one := by simp

/-- Take a homotopy between a plot and a point `y ~ p` and path(0-dim homotopy) `x ~ y` and
return homotopy `x ~ p` -/
noncomputable
def PlotHomotopy.compPathRight {n}
    {X : Type*} [Diffeology X] {p : ℝ^n → X} {x y : X}
    (f : PlotHomotopy (fun _ => y) p)
    (path : PlotHomotopy (fun _ : ℝ^0 => x) (fun _ : ℝ^0 => y)) :
    PlotHomotopy (fun _ : ℝ^n => x) p where

  val := fun ut =>
    let u := FinAdd.fst ut
    let t := FinAdd.snd ut 0
    if t < 1/3 then
      let t' := fun _ => smoothStep (3*t)
      path t' 0
    else if t < 2/3 then
      y
    else
      let t' := fun _ => smoothStep (3*t-2)
      f t' u

  val_is_plot := sorry -- This is currently unprovable as diffeology is missing "Locality axiom"
  val_at_zero := by simp
  val_at_one := by norm_num


/-- Take a path(0-dim homotopy `y ~ p` and path(0-dim homotopy) `x ~ y` and
return homotopy `x ~ p` -/
noncomputable
def PlotHomotopy.compPathLeft {n}
    {X : Type*} [Diffeology X] {p : ℝ^n → X} {x y : X}
    (path : PlotHomotopy (fun _ : ℝ^0 => x) (fun _ : ℝ^0 => y))
    (f : PlotHomotopy p (fun _ => x)) :
    PlotHomotopy p (fun _ : ℝ^n => y) :=
  (f.reverse.compPathRight path.reverse).reverse


def PlotHomotopy.pathBetween {n}
    {X : Type*} [Diffeology X]
    (p : ℝ^n → X) (hp : p ∈ plots n) (u v : ℝ^n) :
    PlotHomotopy (fun _ : ℝ^0 => p u) (fun _ : ℝ^0 => p v) where
  val := fun ut =>
    let t := FinAdd.snd ut 0
    p ((1-t)•u + t•v)

  val_is_plot := plot_comp hp (by fun_prop)
  val_at_zero := by simp
  val_at_one := by simp



open Diffeology Util in
/-- Homotopy between n-plots `p` and a poitn `x`(i.e. constant plot) which is itself (n+1)-plot. -/
def PlotPointHomotopy {X : Type*} [Diffeology X] {n} (p : ℝ^n → X) (x : X) :=
  PlotHomotopy p (fun _ => x)


instance {X : Type*} [Diffeology X] {n} (p : ℝ^n → X) (x : X) :
    DFunLike (PlotPointHomotopy p x) ℝ^1 (fun _ => ℝ^n → X) where
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
theorem PlotPointHomotopy.at_zero {X : Type*} [Diffeology X] {n} (p : ℝ^n → X) (x : X)
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
    (lift : (c : ℝ^1 → X) → (s t : ℝ^1) → E (c s) → E (c t))
    (v : (u : ℝ^n) → E (p u)) : ℝ^n → E x :=
  fun u => cast (by simp) (lift (ht · u) 0 1 (cast (by simp) (v u) : E (ht 0 u)))


/-- The canonical homotopy between a plot `p` and a point `x`. -/
def PlotPointHomotopy.mk {X : Type*} [Diffeology X]
    (p : (Fin n → ℝ) → X) (hp : p ∈ plots n) (x : X) (hx : p 0 = x) : PlotPointHomotopy p x where
  val := fun ut =>
    let u := FinAdd.fst ut
    let t := FinAdd.snd ut
    p ((1-t 0)•u)
  val_is_plot := by
    apply Diffeology.plot_comp
    · exact hp
    · fun_prop
  val_at_zero := by simp
  val_at_one := by simp[hx]


def PlotPointHomotopy.comp {n m}
    {X : Type*} [Diffeology X]
    {p : (Fin n → ℝ) → X} {x : X}
    (ht : PlotPointHomotopy p x)
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ ⊤ f) :
    PlotPointHomotopy (fun u => p (f u)) x where
  val := fun ut =>
    let u := FinAdd.fst ut
    let t := FinAdd.snd ut
    ht t (f u)
  val_is_plot := by
    apply plot_comp
    · exact ht.val_is_plot
    · fun_prop
  val_at_zero := by simp
  val_at_one := by simp


#exit
def covDeriv (f : (x : X) → E x) (x : X) (dx : TX x) : TE _ (f x)  :=
  let c := TangentSpace.curve x dx
  let c' := fun x => f (c x)
  let c' : DiffeologyMap (Fin 1 → ℝ) (Sigma E) := ⟨fun t => ⟨c t, f (c t)⟩, sorry⟩
  let v'' := TangentSpace.tangent c' sorry (fun _ => 0) (fun _ => 1)
  cast (by simp[c',c]; rw[TangentSpace.curve_at_zero]) v''.2
