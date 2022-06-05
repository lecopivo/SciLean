 import SciLean.Core.Functions

import SciLean.Core.Monad.VecMonad

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 100000

namespace SciLean

def compM {X Y Z} {m} [Monad m] (f : Y → m Z) (g : X → m Y) : X → m Z :=
  λ x => g x >>= f

def idM {X} {m} [Monad m] : X → m X := λ x => pure x

def mapM {X m} [Monad m] (f : X → Y) : X → m Y := λ x => pure (f x)

def compFD {X Y Z : Type} (Tf : Y → Z×(Y→Z)) (Tg : X → Y×(X→Y)) : X → Z×(X→Z) := 
  λ x => 
    let (y, dg) := Tg x
    let (z, df) := Tf y
    (z, λ dx => df (dg dx))

def idFD {X} : X → X×(X→X) := λ x => (x, λ dx => dx)

def compFDM {X Y Z : Type} {m} [Monad m] 
  (Tf : Y → m (Z × (Y → m Z))) 
  (Tg : X → m (Y × (X → m Y))) 
  : X → m (Z × (X → m Z)) :=
  λ x => do
    let (y, dy) ← Tg x
    let (z, dz) ← Tf y
    pure (z, λ dx => dy dx >>= dz)

def appFDM {X Y Z : Type} {m} [Monad m] 
  (Tf : Y → m (Z × (Y → m Z))) 
  : (Y × (X → m Y)) → m (Z × (X → m Z)) :=
  λ (y,dy) => do
    let (z, dz) ← Tf y
    pure (z, λ dx => dy dx >>= dz)

def mapFDM {X Y: Type} {m} [Monad m] 
  (Tf : X → (Y × (X → Y)))
  : X → m (Y × (X → m Y)) := λ x => 
    let (y,df) := Tf x
    pure (y, λ dx => pure (df dx))

@[simp]
theorem compFDM_appFDM
  {X Y Z : Type} {m} [Monad m] 
  (Tf : Y → m (Z × (Y → m Z))) 
  (Tg : X → m (Y × (X → m Y))) 
  (x : X)
  : compFDM Tf Tg x = Tg x >>= appFDM Tf  :=
by
  simp[compFDM,appFDM]; done


def idFDM {X : Type} {m} [Monad m]
    : X → m (X × (X → m X)) :=
    λ x => pure (x, λ dx => pure dx)

def fmaplrFDM {X Y Z : Type} {m} [Monad m]
  (Tf : X → m (Y × (X → m Y))) 
  (Tg : X → m (Z × (X → m Z))) 
  : X → m ((Y×Z) × (X → m (Y×Z))) :=
  λ x => do
    let (y, df) ← Tf x
    let (z, dg) ← Tg x
    pure ((y,z), λ dx => do pure (← df dx, ← dg dx))

class FwdDiffMonad (m : Type → Type) extends VecMonad m where
  IsSmoothM {X} [Vec X] (mx : m X) : Prop

  pure_is_smooth {X} [Vec X] : IsSmooth (λ x : X => (pure x : m X))
  pure_is_smoothM {X} [Vec X] (x : X) : IsSmoothM (pure x : m X)

  bind_is_smooth {X Y Z} [Vec X] [Vec Y] [Vec Z]
    (f : Y → m Z) (hf₁ : IsSmooth f) (mhf₂ : ∀ y, IsSmoothM (f y))
    (g : X → m Y) (hg₁ : IsSmooth g) (mhg₂ : ∀ x, IsSmoothM (g x))
    : IsSmooth (compM f g)
  bind_is_smoothM {X Y} [Vec X] [Vec Y]
    (f : X → m Y) (hf₁ : IsSmooth f) (mhf₂ : ∀ x, IsSmoothM (f x))
    (mx : m X) (hx : IsSmoothM mx)
    : IsSmoothM (mx >>= f)

  diag_is_smooth {X Y Z} [Vec X] [Vec Y] [Vec Z]
    (f : X → m Y) (hf₁ : IsSmooth f) (hf₂ : ∀ x, IsSmoothM (f x))
    (g : X → m Z) (hg₁ : IsSmooth g) (hg₂ : ∀ x, IsSmoothM (g x))
    : IsSmooth λ x => (do pure (← f x, ← g x) : m (Y×Z))
  diag_is_smoothM {X Y} [Vec X] [Vec Y]
    (mx : m X) (hx : IsSmoothM mx)
    (my : m Y) (hy : IsSmoothM my)
    : IsSmoothM (do pure (← mx, ← my))

  fwdDiffM {X Y} [Vec X] [Vec Y] (f : X → m Y) 
    : X → m (Y × (X → m Y))
  fwdDiffM_id {X} [Vec X] 
    : fwdDiffM (idM : X → m X) = idFDM
  fwdDiffM_comp {X Y Z} [Vec X] [Vec Y] [Vec Z] 
    (f : Y → m Z) [IsSmooth f] (hf₂ : ∀ y, IsSmoothM (f y))
    (g : X → m Y) [IsSmooth g] (hf₂ : ∀ x, IsSmoothM (g x))
    : fwdDiffM (compM f g) = compFDM (fwdDiffM f) (fwdDiffM g)

  -- mapFDM {X Y} [Vec X] [Vec Y] (f : X → Y×(X → Y)) 
  --   : X → m (Y × (X → m Y))
  mapFDM_id {X} [Vec X]
    : mapFDM (m:=m) (idFD (X:=X)) = idFDM
  mapFDM_comp {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : Y → Z×(Y→Z)) (g : X → Y×(X→Y))
    : mapFDM (m:=m) (compFD f g) = compFDM (mapFDM f) (mapFDM g)

  fwdDiff_fwdDiffM {X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f] 
    : fwdDiffM (mapM f) = mapFDM (fwdDiff f)

  const_fwdDiffM {X Y : Type} [Vec X] [Vec Y] 
    (mx : m X) (hx : IsSmoothM mx)
    : fwdDiffM (λ y : Y => mx) = 
      (λ y => do
        let xdx ← fwdDiffM (λ _ : Unit => mx) ()
        pure (xdx.1, λ dy => xdx.2 ()))

  diag_fwdDiffM {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
    (f : X → m Y) [IsSmooth f] (hf₂ : ∀ x, IsSmoothM (f x))
    (g : X → m Z) [IsSmooth g] (hg₂ : ∀ x, IsSmoothM (g x))
    : fwdDiffM (λ x => do pure (← f x, ← g x)) = fmaplrFDM (fwdDiffM f) (fwdDiffM g)

export FwdDiffMonad (fwdDiffM)

class IsSmoothM {X} [Vec X] {m} [FwdDiffMonad m] (mx : m X) : Prop where
  is_smoothM  : FwdDiffMonad.IsSmoothM mx

    
