import SciLean.Core.Monads.FwdDerivMonad
import SciLean.Core.Monads.RevDerivMonad

namespace SciLean


section FwdDerivMonad

variable 
  {K : Type _} [IsROrC K]
  {m : Type → Type} {m' : outParam $ Type → Type} [Monad m] [Monad m'] [FwdDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']


noncomputable
instance (S : Type _) [Vec K S] : FwdDerivMonad K (StateT S m) (StateT (S×S) m') where
  fwdDerivM f := fun x dx sds => do
    -- ((y,s'),(dy,ds'))
    let r ← fwdDerivM K (fun (xs : _×S) => f xs.1 xs.2) (x,sds.1) (dx,sds.2)
    -- ((y,dy),(s',ds'))
    pure ((r.1.1,r.2.1),(r.1.2, r.2.2))

  IsDifferentiableM f := IsDifferentiableM K (fun (xs : _×S) => f xs.1 xs.2)

  fwdDerivM_pure f h := 
    by 
      simp[pure, StateT.pure, fwdCDeriv]
      funext x dx sds
      ftrans
      simp [fwdCDeriv]
      
  fwdDerivM_bind f g hf hg :=
    by 
      funext x dx sds
      simp at hf; simp at hg
      simp[fwdCDeriv, bind, StateT.bind, StateT.bind.match_1]
      ftrans

  fwdDerivM_pair f hf := 
    by
      funext x dx sds
      simp at hf
      simp[bind, StateT.bind, StateT.bind.match_1, pure, StateT.pure]
      ftrans only
      simp

  IsDifferentiableM_pure f hf :=
    by 
      simp; simp at hf
      fprop

  IsDifferentiableM_bind f g hf hg := 
    by
      simp; simp at hf; simp at hg
      simp[bind, StateT.bind, StateT.bind.match_1]
      fprop

  IsDifferentiableM_pair f hf := 
    by
      simp; simp at hf
      simp[bind, StateT.bind, StateT.bind.match_1, pure, StateT.pure]
      fprop

end FwdDerivMonad


section RevDerivMonad

variable 
  {K : Type _} [IsROrC K]
  {m : Type → Type} {m' : outParam $ Type → Type} [Monad m] [Monad m'] [RevDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']

noncomputable
instance (S : Type _) [SemiInnerProductSpace K S] : RevDerivMonad K (StateT S m) (StateT S m') where
  revDerivM f := fun x s => do
    let ysdf ← revDerivM K (fun (xs : _×S) => f xs.1 xs.2) (x,s)
    pure ((ysdf.1.1, fun dx ds => ysdf.2 (dx,ds)), ysdf.1.2)

  HasAdjDiffM f := HasAdjDiffM K (fun (xs : _×S) => f xs.1 xs.2)

  revDerivM_pure f h := 
    by 
      simp[pure, StateT.pure, revCDeriv]
      funext x s
      ftrans
      simp [revCDeriv]
      
  revDerivM_bind f g hf hg :=
    by 
      funext x s
      simp at hf; simp at hg
      simp[revCDeriv, bind, StateT.bind, StateT.bind.match_1]
      ftrans
      simp
      congr

  revDerivM_pair f hf := 
    by
      funext x s
      simp at hf
      simp[bind, StateT.bind, StateT.bind.match_1, pure, StateT.pure]
      ftrans only
      simp
      congr; funext ysdf; congr; funext dx ds; congr; funext (dx,ds); simp

  HasAdjDiffM_pure f hf :=
    by 
      simp; simp at hf
      fprop

  HasAdjDiffM_bind f g hf hg := 
    by
      simp; simp at hf; simp at hg
      simp[bind, StateT.bind, StateT.bind.match_1]
      fprop

  HasAdjDiffM_pair f hf := 
    by
      simp; simp at hf
      simp[bind, StateT.bind, StateT.bind.match_1, pure, StateT.pure]
      fprop

end RevDerivMonad
