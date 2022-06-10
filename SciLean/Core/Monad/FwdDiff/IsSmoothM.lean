import SciLean.Core.Monad.FwdDiff.Basic

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 100000

namespace SciLean

variable {α β γ}
variable {X Y Z Y₁ Y₂} [Vec X] [Vec Y] [Vec Z] [Vec Y₁] [Vec Y₂]
variable {m} [FwdDiffMonad m]

instance pure.arg_x.isSmooth  : IsSmooth (λ x => (pure x : m X)) :=
by
  apply FwdDiffMonad.pure_is_smooth

instance pure.isSmoothM (x : X) : IsSmoothM (pure x : m X) :=
by
  constructor
  apply FwdDiffMonad.pure_is_smoothM

instance bind.isSmoothM 
  (f : X → m Y) [hf₁ : IsSmooth f] [hf₂ : ∀ x, IsSmoothM (f x)]
  (mx : m X) [hx : IsSmoothM mx]
  : IsSmoothM (mx >>= f) :=
by
  constructor
  apply FwdDiffMonad.bind_is_smoothM f hf₁ (λ x => (hf₂ x).1) mx hx.1

instance mapM.arg_f.isSmooth
  : IsSmooth (λ f : X → Y => mapM (m:=m) f) := by simp[mapM] infer_instance
instance mapM.arg_x.isSmooth
  (f : X → Y) [IsSmooth f]
  : IsSmooth (λ x => mapM (m:=m) f x) := by simp[mapM] infer_instance
instance mapM.arg_x.isSmoothM
  (f : X → Y) [IsSmooth f] (x : X)
  : IsSmoothM (mapM (m:=m) f x) := by simp[mapM] infer_instance


instance compM.arg_x.isSmooth
  (f : Y → m Z) [hf₁ : IsSmooth f] [hf₂ : ∀ x, IsSmoothM (f x)]
  (g : X → m Y) [hg₁ : IsSmooth g] [hg₂ : ∀ x, IsSmoothM (g x)] 
  : IsSmooth (λ x => g x >>= f) := 
by 
  apply FwdDiffMonad.bind_is_smooth f hf₁ (λ x => (hf₂ x).1) g hg₁ (λ x => (hg₂ x).1)

instance compM.arg_x.isSmoothM
  (f : Y → m Z) [hf₁ : IsSmooth f] [hf₂ : ∀ x, IsSmoothM (f x)]
  (g : X → m Y) [hg₁ : IsSmooth g] [hg₂ : ∀ x, IsSmoothM (g x)] 
  (x : X)
  : IsSmoothM (g x >>= f) := by infer_instance

instance diagPairM.arg_x.isSmooth
  (f : X → m Y) [hf₁ : IsSmooth f] [hf₂ : ∀ x, IsSmoothM (f x)]
  (g : X → m Z) [hg₁ : IsSmooth g] [hg₂ : ∀ x, IsSmoothM (g x)]
  : IsSmooth λ x => (do pure (← f x, ← g x) : m (Y×Z)) :=
by
  apply FwdDiffMonad.diag_is_smooth f hf₁ (λ x => (hf₂ x).1) g hg₁ (λ x => (hg₂ x).1)

instance diagPairM.arg_x.isSmoothM
  (mx : m X) [hx : IsSmoothM mx]
  (my : m Y) [hy : IsSmoothM my]
  : IsSmoothM (do pure (← mx, ← my) : m (X × Y)) := 
by 
  constructor
  apply FwdDiffMonad.diag_is_smoothM mx hx.1 my hy.1

instance scombM.arg_x.isSmooth
  (f : X → Y → m Z) [IsSmooth f] [∀ x, IsSmooth (f x)] [∀ x y, IsSmoothM (f x y)]
  (g : X → m Y) [IsSmooth g] [∀ x, IsSmoothM (g x)]
  : IsSmooth λ x => (do f x (← g x) : m Z) := 
by
  
  let f₁ : X → m (X × Y) := λ x => do pure (← pure x, ← g x)
  let f₂ : X × Y → m Z := λ xy => f xy.1 xy.2
  
  have h :
     (λ x => (do f x (← g x) : m Z))
     =
     λ x => f₁ x >>= f₂
     := by simp;
  rw[h]
  infer_instance

instance scombM.arg_x.isSmoothM
  (f : X → Y → m Z) [IsSmooth f] [∀ x, IsSmooth (f x)] [∀ x y, IsSmoothM (f x y)]
  (g : X → m Y) [IsSmooth g] [∀ x, IsSmoothM (g x)]
  (mx : m X) [IsSmoothM mx]
  : IsSmoothM (do let x ← mx; f x (← g x) : m Z) := 
by
  
  let f₁ : X → m (X × Y) := λ x => do pure (← pure x, ← g x)
  let f₂ : X × Y → m Z := λ xy => f xy.1 xy.2
  
  have h :
     (do let x ← mx; f x (← g x) : m Z)
     =
     mx >>= f₁ >>= f₂
     := by simp;
  rw[h]
  infer_instance


instance diagM.arg_x.isSmoothM
  (f : Y₁ → Y₂ → m Z) [IsSmooth f] [∀ x, IsSmooth (f x)] [∀ x y, IsSmoothM (f x y)]
  (g₁ : X → m Y₁) [IsSmooth g₁] [∀ x, IsSmoothM (g₁ x)]
  (g₂ : X → m Y₂) [IsSmooth g₂] [∀ x, IsSmoothM (g₂ x)]
  (mx : m X) [IsSmoothM mx]
  : IsSmoothM (do let x ← mx; f (← g₁ x) (← g₂ x) : m Z) := 
by infer_instance
 
instance diagM.arg_x.isSmooth
  (f : Y₁ → Y₂ → m Z) [IsSmooth f] [∀ x, IsSmooth (f x)] [∀ x y, IsSmoothM (f x y)]
  (g₁ : X → m Y₁) [IsSmooth g₁] [∀ x, IsSmoothM (g₁ x)]
  (g₂ : X → m Y₂) [IsSmooth g₂] [∀ x, IsSmoothM (g₂ x)]
  : IsSmooth λ x => (do f (← g₁ x) (← g₂ x) : m Z) := 
by infer_instance

-- instance fmap.arg_x.isSmooth
--   (g₁ : X → m Y₁) [IsSmooth g₁] [∀ x, IsSmoothM (g₁ x)]
--   (g₂ : X → m Y₂) [IsSmooth g₂] [∀ x, IsSmoothM (g₂ x)]
--   : IsSmooth λ x => (do pure (← g₁ x, ← g₂ x) : m (Y₁ × Y₂)) := by infer_instance

-- instance fmap.arg_x.isSmoothM
--   (g₁ : X → m Y₁) [IsSmooth g₁] [∀ x, IsSmoothM (g₁ x)]
--   (g₂ : X → m Y₂) [IsSmooth g₂] [∀ x, IsSmoothM (g₂ x)] (x : X) 
--   : IsSmoothM (do pure (← g₁ x, ← g₂ x) : m (Y₁ × Y₂)) := by infer_instance

----------------------------------------------------------------------

-- instance compM.arg_x.parm_a.isSmooth
--   (a : α)
--   (f : Y → α → m Z) [hf₁ : IsSmooth (λ y => f y a)] [hf₂ : ∀ y, IsSmoothM (λ f y a)]
--   (g : X → m Y) [hg₁ : IsSmooth g] [hg₂ : ∀ x, IsSmoothM (g x)] 
--   : IsSmooth (λ x => g x >>= f) := 
-- by 
--   apply FwdDiffMonad.bind_is_smooth f hf₁ (λ x => (hf₂ x).1) g hg₁ (λ x => (hg₂ x).1)

  
section Tests

  example 
    : IsSmooth λ (x : X) => (pure x : m X) := by infer_instance

  example {α} (f : X → Y) [IsSmooth f] 
    : IsSmooth λ (x : X) (a : α) => f x := by infer_instance

  example (f : X → m X) [IsSmooth f] [∀ x, IsSmoothM (f x)]
    : IsSmooth λ x : X => (do f x >>= f >>= f >>= f : m X) := 
  by infer_instance

  example (f : X → m X) [IsSmooth f] [∀ x, IsSmoothM (f x)]
    (mx : m X) [IsSmoothM mx]
    : IsSmoothM (mx >>= f >>= f >>= f >>= f) := 
  by infer_instance

  example (f : X → m X) [IsSmooth f] [∀ x, IsSmoothM (f x)]
    : IsSmooth λ x : X => (do 
      let fx ← f x
      let x' := fx + x
      pure fx : m X) := 
  by infer_instance

  example (f : X → m X) [IsSmooth f] [∀ x, IsSmoothM (f x)]
    : IsSmooth λ x : X => (do 
      let fx ← f x
      pure x : m X) := 
  by
    infer_instance

  example (f : X → m X) [IsSmooth f] [∀ x, IsSmoothM (f x)]
    (mx : m X) [IsSmoothM mx]
    : IsSmoothM (do 
      let x ← mx
      let fx ← f x
      pure x : m X) := 
  by 
    infer_instance

  example (f : X → m X) [IsSmooth f] [∀ x, IsSmoothM (f x)]
    (mx : m X) [IsSmoothM mx]
    : IsSmoothM (do 
      let a ← mx
      let b ← f a
      let c ← f b
      pure (a + b ) : m X) := 
  by 
    infer_instance

end Tests


