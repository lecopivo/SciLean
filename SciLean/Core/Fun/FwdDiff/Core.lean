import SciLean.Core.Fun.Diff

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z] 
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

noncomputable 
def fwdDiff (f : X → Y) : X → Y×(X → Y) := λ x => (f x, λ dx => ∂ f x dx)

prefix:max "𝓣" => fwdDiff

theorem fwdDiff_of_linear (f : X → Y) [IsLin f] : fwdDiff f = λ x => (f x, f) :=
by 
  simp [fwdDiff]
  rw[diff_of_linear]
  done

def fmapFD {α : Type} (f : X×(α → X) → Y×(α → Y)) (g : X×(α → X) → Z×(α → Z))
  : X×(α → X) → (Y×Z)×(α → Y×Z)
  :=
  λ xdx =>
    let (y,dy) := f xdx
    let (z,dz) := g xdx
    ((y, z), λ a => (dy a, dz a))

def appFD
  (Tf : Y → (Z × (Y → Z))) 
  : (Y × (X → Y)) → (Z × (X → Z)) :=
  λ (y,dy) =>
    let (z, dz) := Tf y
    (z, λ dx => dz (dy dx))

-- Computale version of `fwdDiff eval` where you specify the `Tf = fwdDiff f` explicitely
def evalFD {α : Type} (fxdfdx : ((X → Y) × X) × (α → (X → Y) × X)) (Tf : (X × (α → X)) → (Y × (α → Y)))
  : Y × (α → Y)
  := 
  let ((f,x),dfdx) := fxdfdx
  let (y, dy) := Tf (x, λ a => (dfdx a).2)
  (y, λ a => (dfdx a).1 x + dy a)

-- @[simp ↓]
-- theorem eval_fwdDiff (f : X → Y) [IsSmooth f] (x : X) (dfdx : α → (X → Y) × X)
--   : fwdDiff α (λ ((f,x) : (X → Y) × X) => f x) ((f,x),dfdx) = evalFD ((f,x),dfdx) (fwdDiff α f)
--   :=
-- by
--   simp[fwdDiff,evalFD] done

def uncurryFD {α : Type} (Tf : X×(α → X) → (Y→Z)×(α → Y → Z)) (Tfx : X → Y×(α → Y) → Z×(α → Z)) 
  : (X×Y)×(α → X×Y) → Z×(α → Z)
  :=
  λ ((x, y), dxy) =>
    let (fx, df) := Tf (x, λ a => (dxy a).1)
    let (z, dfx) := Tfx x (y, λ a => (dxy a).2)
    (z, λ a => df a y + dfx a)

-- @[simp ↓]
-- theorem uncurry_fwdDiff (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
--   : fwdDiff α (Function.uncurry f) = uncurryFD (fwdDiff α f) (λ x => fwdDiff α (f x))
--   := by
--   simp[fwdDiff,Function.uncurry,uncurryFD] done

----------------------------------------------------------------------

@[simp ↓, simp_diff]
theorem id.arg_x.fwdDiff_simp
  : fwdDiff (λ x : X => x) = λ x => (x, λ dx => dx) := by simp[fwdDiff] done

@[simp ↓, simp_diff]
theorem const.arg_y.fwdDiff_simp (x : X)
  : fwdDiff (λ y : Y => x) = λ y => (x, λ _ => 0) := by simp[fwdDiff] done

@[simp ↓ low-3]
theorem swap.arg_x.fwdDiff_simp (f : α → X → Y) [∀ i, IsSmooth (f i)]
  : fwdDiff (λ x a => f a x) = 
           λ x => 
           let Tf := λ a => fwdDiff (f a)
           (λ a => (Tf a x).1, λ dx a => (Tf a x).2 dx) := 
by 
  simp[fwdDiff] done


@[simp ↓ low-2, simp_diff low-2]
theorem scomb.arg_x.fwdDiff_simp
  (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
  (g : X → Y) [IsSmooth g] 
  : fwdDiff (λ x => f x (g x))
    = 
    λ x =>
      let (y, dy) := fwdDiff g x
      let Tf      := fwdDiff (hold λ (x', y') => f x' y')
      appFD Tf ((x,y), λ dx => (dx, dy dx))
    := 
  by 
    simp[fwdDiff,fmapFD,evalFD,appFD,hold] done

@[simp ↓ low-1, simp_diff low-1]
theorem comp.arg_x.fwdDiff_simp
  (f : Y → Z) [IsSmooth f] 
  (g : X → Y) [IsSmooth g] 
  : fwdDiff (λ x => f (g x)) 
    = 
    λ x => appFD (fwdDiff f) (fwdDiff g x) 
  := 
by 
  unfold fwdDiff
  simp[appFD]
  done

@[simp ↓ low, simp_diff low]
theorem parm.arg_x.fwdDiff_simp
  (f : X → α → Y) [IsSmooth f] (a : α)
  : fwdDiff (λ x => f x a) = λ x => 
      let (fx,dfx) := fwdDiff f x
      (fx a, λ dx => dfx dx a)
  := 
by 
  simp [fwdDiff] done
