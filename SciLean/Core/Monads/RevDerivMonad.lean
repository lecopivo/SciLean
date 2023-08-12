import SciLean.Core.FunctionTransformations.RevCDeriv

namespace SciLean


set_option linter.unusedVariables false in
class RevDerivMonad (K : Type) [IsROrC K] (m : Type → Type) (m' : outParam $ Type → Type) [Monad m] [Monad m'] where
  revDerivM {X : Type} {Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] : ∀ (f : X → m Y) (x : X), m (Y × (Y → m' X))
  revDerivValM : ∀ {X} [Vec K X], m X → m (X × (X → m' Unit))

  HasAdjDiffM {X : Type} {Y : Type} [Vec K X] [Vec K Y]
    : ∀ (f : X → m Y), Prop
  HasAdjDiffValM {X : Type} [Vec K X]
    : ∀ (x : m X), Prop

  revDerivM_pure {X Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] (f : X → Y) (hf : HasAdjDiff K f)
    : revDerivM (fun x => pure (f:=m) (f x)) = fun x => let ydf := revCDeriv K f x; pure (ydf.1, fun dy => pure (ydf.2 dy))
  fwdDerivM_bind 
    {X Y Z : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] [SemiInnerProductSpace K Z] 
    (f : Y → m Z) (g : X → m Y) (hf : HasAdjDiffM f) (hg : HasAdjDiffM g)
     : revDerivM (fun x => g x >>= f) 
       = 
       fun x => do
         let ydg ← revDerivM g x
         let zdf ← revDerivM f ydg.1
         pure (zdf.1, fun dz => zdf.2 dz >>= ydg.2)
  fwdDerivM_const {X Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] (y : m Y) (hy : HasAdjDiffValM y)
    : revDerivM (fun _ : X => y) = fun _ => do let ydy ← revDerivValM y; pure (ydy.1, fun dx => do let _ ← ydy.2 dx; pure 0)
  fwdDerivM_pair {X : Type} {Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] -- is this really necessary?
    (f : X → m Y) (hf : HasAdjDiffM f)
    : revDerivM (fun x => do let y ← f x; pure (x,y))
      =
      (fun x => do
        let ydf ← revDerivM f x
        pure ((x,ydf.1), fun dxy : X×Y => do let dx ← ydf.2 dxy.2; pure (dxy.1 + dx)))


  IsDifferentiableM_pure {X : Type} {Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] (f : X → Y)
    : IsDifferentiable K f ↔ IsDifferentiableM (fun x : X => pure (f x))
  IsDifferentiableM_bind {X Y Z: Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] [SemiInnerProductSpace K Z]
    (f : Y → m Z) (g : X → m Y) 
    (hf : IsDifferentiableM f) (hg : IsDifferentiableM g)
    : IsDifferentiableM (fun x => g x >>= f)
  IsDifferentiableM_const {X : Type} {Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y]
    : ∀ (y : m Y), IsDifferentiableValM y ↔ IsDifferentiableM (fun _ : X => y)
  IsDifferentiableM_pair {X : Type} {Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] -- is this really necessary?
    (f : X → m Y) (hf : IsDifferentiableM f)
    : IsDifferentiableM (fun x => do let y ← f x; pure (x,y))
