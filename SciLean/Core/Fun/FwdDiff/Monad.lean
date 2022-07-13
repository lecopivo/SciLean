import SciLean.Core.Monad.VecMonad
import SciLean.Core.Fun.FwdDiff.Core
import SciLean.Core.Functions

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

-- mapFD == fwdDiff

def compFDM {X Y Z : Type} {m} [Monad m] 
  (Tf : Y → m (Z × (Y → m Z))) 
  (Tg : X → m (Y × (X → m Y))) 
  : X → m (Z × (X → m Z)) :=
  λ x => do
    let (y, dy) ← Tg x
    let (z, dz) ← Tf y
    pure (z, λ dx => dy dx >>= dz)

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

  
class FwdDiffMonad (m : Type → Type) extends VecMonad m, IgnoreEffect m where
  IsSmoothM {X} [Vec X] (mx : m X) : Prop
  
  fwdDiffM {X Y} [Vec X] [Vec Y] (f : X → m Y) 
    : X → m (Y × (X → m Y))

  fwdDiffM_id {X} [Vec X] 
    : fwdDiffM (idM : X → m X) = idFDM

  fwdDiffM_comp {X Y Z} [Vec X] [Vec Y] [Vec Z] 
    (f : Y → m Z) [IsSmooth f] (hf₂ : ∀ y, IsSmoothM (f y))
    (g : X → m Y) [IsSmooth g] (hf₂ : ∀ x, IsSmoothM (g x))
    : fwdDiffM (compM f g) = compFDM (fwdDiffM f) (fwdDiffM g)

  mapFDM {X Y} [Vec X] [Vec Y] (f : X → Y×(X → Y)) 
    : X → m (Y × (X → m Y))

  mapFDM_id {X} [Vec X]
    : mapFDM (idFD (X:=X)) = idFDM

  mapFDM_comp {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : Y → Z×(Y→Z)) (g : X → Y×(X→Y))
    : mapFDM (compFD f g) = compFDM (mapFDM f) (mapFDM g)

  fwdDiff_fwdDiffM {X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f] 
    : fwdDiffM (mapM f) = mapFDM (fwdDiff f)

  -- uncurryD {X Y Z} [Vec X] [Vec Y] [Vec Z] (α : Type)
  --   (Tf : X×(α → m X) → m ((Y → m Z) × (α → m (Y → m Z))))
  --   (Tfx : X → (Y × (α → m Y)) → m (Z × (α → m Z)))
  --   : (X×Y) × (α → m (X×Y)) → m (Z × (α → m Z))

  fmap_fwdDiffM {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
    (f : X → m Y) [IsSmooth f] (hf₂ : ∀ x, IsSmoothM (f x))
    (g : X → m Z) [IsSmooth g] (hg₂ : ∀ x, IsSmoothM (g x))
    : fwdDiffM (λ x => do pure (← f x, ← g x)) = fmaplrFDM (fwdDiffM f) (fwdDiffM g)


-- @[addPush]
-- theorem add_push_lin {X Y} [Vec X] [Vec Y] (f : X → Y) [IsLin f] (x x' : X)
--   : f x + f x' = f (x + x') := sorry

-- @[addPull]
-- theorem add_pull_differential {X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f] (x dx dx' : X)
--   : ∂ f x (dx + dx') = ∂ f x dx + ∂ f x dx' := sorry

-- @[addPull]
-- theorem add_pull_prod_fst {X Y} [Add X] [Add Y] (xy xy' : X×Y)
--   : (xy + xy').1 = xy.1 + xy'.1 := sorry

-- @[addPull]
-- theorem add_pull_prod_snd {X Y} [Add X] [Add Y] (xy xy' : X×Y)
--   : (xy + xy').2 = xy.2 + xy'.2 := sorry

-- noncomputable
-- instance {σ} [Vec σ] : FwdDiffMonad (StateM σ) where
--   IsSmoothM mx := IsSmooth (λ s => mx s)
  
--   fwdDiffM f := λ x s => 
--      let ((y,s), df) := fwdDiff (λ (x,s) => f x s) (x,s)
--      ((y, λ dx ds => df (dx,ds)), s)

--   fwdDiffM_id := by simp[pure,StateT.pure,StateM,StateT,Id,prod_add_elemwise,idFDM,idM]

--   fwdDiffM_comp f hf₁ mhf₂ g hg₁ mhg₂ := by
--     simp[fwdDiff,compM,compFDM,pureZero, pure,StateT.pure,bind,StateT.bind,StateT,StateM,Id,prod_add_elemwise,uncurryFDM,fmaplrFDM] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
--     have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x)
--     have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y)
--     funext x s; simp
--     done

--   mapFDM Tf := λ x s => 
--     let (y,df) := Tf x
--     ((y, λ dx ds => (df dx, ds)), s)

--   mapFDM_id := by simp[pure,StateT.pure,idFD,idFDM]

--   mapFDM_comp Tf Tg := by 
--     simp[bind,StateT.bind,pure,StateT.pure,idFD,idFDM,compFDM,compFD]

--   fwdDiff_fwdDiffM f _ := by 
--     simp[fwdDiff,pure,StateT.pure,StateT,StateM,Id,prod_add_elemwise,mapM]

--   fmap_fwdDiffM f hf₁ mhf₂ g hg₁ mhg₂ := by
--     simp[fwdDiff,compM,compFDM,pureZero, pure,StateT.pure,bind,StateT.bind,StateT,StateM,Id,prod_add_elemwise,uncurryFDM,fmaplrFDM] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
--     have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x)
--     have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y)
--     funext x s; simp[prod_add_elemwise]
--     done
    

  -- uncurryD α Tf Tfx := λ ((x,y), dxy) s => 
  --   let xdx := (x, λ a ds => ((dxy a ds).1.1,(dxy a ds).2))
  --   let ydy := (y, λ a ds => ((dxy a ds).1.2,(dxy a ds).2))
  --   let ((fx, df'),s) := Tf xdx s
  --   let df : α → StateM σ _ := λ a (ds : σ) => (df' a ds).1 y s -- This is an odd operations
  --   let ((z,  dfx),s) := Tfx x ydy s
  --   ((z, df + dfx), s)

  -- diagD α Tf Tg₁ Tg₂ := λ xdx s => sorry

  -- pairD α Tf Tg := λ xdx s => 
  --   let ((y,dy),s) := Tf xdx s
  --   let ((z,dz),s) := Tg xdx s
  --   (((y,z), 
  --     λ a ds => 
  --       let (dy,dsdy) := dy a ds
  --       let (dz,dsdz) := dz a ds
  --       ((dy,dz), dsdy + dsdz)),
  --    s)

  -- curry_fwdDiff f hf₁ hf₂ mhf₃ := by 
  --   simp[uncurryFDM,bind,StateT.bind,pure,StateT.pure,StateM,StateT,Id,fwdDiff,pureZero] at f hf₁ hf₂ mhf₃ ⊢
  --   funext x s; simp
  --   funext a ds; simp
  --   have h : ∀ {X} [Vec X] (a b c : X), a + b + c = a + (b + c) := sorry;
  --   rw[h];

  -- pair_fwdDiff f hf₁ mhf₂ := by
  --   simp[uncurryFDM,bind,StateT.bind,pure,StateT.pure,StateM,StateT,Id,fwdDiff,pureZero,ignoreEffect] at f hf₁ mhf₂ ⊢
  --   have hf₂ : ∀ x, IsSmooth (f x) := λ x => (mhf₂ x)
  --   funext x s; simp
  --   funext a ds; simp[prod_add_elemwise]


  -- pairD_fwdDiff f hf₁ mhf₂ g hg₁ mhg₂ := by
  --   simp[uncurryFDM,bind,StateT.bind,pure,StateT.pure,StateM,StateT,Id,fwdDiff,pureZero,ignoreEffect,prod_add_elemwise] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
  --   have hf₂ : ∀ x, IsSmooth (f x) := λ x => (mhf₂ x)
  --   have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x)
  --   funext x s; simp[prod_add_elemwise]
  --   funext a ds; simp[prod_add_elemwise]
  --   simp[addPull]
  


  -- pureFD Tf := λ (x,dx) => ((Tf (x, default)).1, λ a ds => ((Tf (x, λ a' => (dx a' ds).1)).2 a, (dx a ds).2))

  -- pure_fwdDiffM f := by 
  --   intro _; simp[pure,StateT.pure, StateT, StateM, Id, prod_add_elemwise, fwdDiff, Function.comp]

  -- id_fwdDiffM := by
  --   simp[pure,StateT.pure,StateT,StateM,Id,prod_add_elemwise]

  -- comp_fwdDiffM f hf₁ mhf₂ g hg₁ mhg₂ := by
  --   simp[pureZero, pure,StateT.pure,bind,StateT.bind,StateT,StateM,Id,prod_add_elemwise,uncurryFDM,fmaplrFDM] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
  --   funext xdx s; simp
  --   funext a ds; simp
  --   have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x)
  --   have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y)
  --   simp
  --   constructor 
  --   { admit }
  --   { admit }
    

  -- fmaplrM_fwdDiffM f hf₁ mhf₂ g hg₁ mhg₂ := by
  --   simp[pureZero, pure,StateT.pure,bind,StateT.bind,StateT,StateM,Id,prod_add_elemwise,uncurryFDM,fmaplrFDM,fmaplrM] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
  --   funext xdx s; simp
  --   funext a ds ; simp
  --   have hf₂ : ∀ x, IsSmooth (f x) := λ x => (mhf₂ x)
  --   have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x)
  --   simp[prod_add_elemwise]
  --   constructor
  --   { admit }
  --   { admit }

  -- scomb_fwdDiffM f hf₁ hf₂ mhf₃ g hg₁ mhg₂ := by
  --   simp[pureZero, pure,StateT.pure,bind,StateT.bind,StateT,StateM,Id,prod_add_elemwise,uncurryFDM,fmaplrFDM] at f hf₁ hf₂ mhf₃ g hg₁ mhg₂ ⊢
  --   funext xdx s; simp
  --   funext a ds; simp
  --   have hh1 : ∀ s : σ, IsSmooth (λ x => (g x s).1) := by infer_instance
  --   have hh2 : ∀ s : σ, IsSmooth (λ x => (g x s).2) := by infer_instance
  --   have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x)
  --   have hf₃ : ∀ x y, IsSmooth (f x y) := λ x y => (mhf₃ x y)
  --   -- simp
  --   simp[prod_add_elemwise]
  --   simp
  --   sorry
