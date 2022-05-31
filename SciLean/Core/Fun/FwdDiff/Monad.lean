import SciLean.Core.Monad.VecMonad
import SciLean.Core.Fun.FwdDiff.Core
import SciLean.Core.Functions

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 100000

namespace SciLean

def fmaplrM {m} [Monad m] (f : X → m Y) (g : X → m Z)
  : X → m (Y×Z)
  := λ x => do
  let y ← f x
  let z ← g x
  pure (y, z)

def fmaprM {m} [Monad m] (f : X → Y) (g : X → m Z)
  : X → m (Y×Z)
  := λ x => do
  let y := f x
  let z ← g x
  pure (y, z)

def fmaprlM {m} [Monad m] (f : X → m Y) (g : X → m Z)
  : X → m (Y×Z)
  := λ x => do
  let z ← g x
  let y ← f x
  pure (y, z)

def fmaplrFDM {Y Z} [Vec Y] [Vec Z] {α : Type} {m} [VecMonad m] 
  (f : X×(α → m X) → m (Y×(α → m Y))) 
  (g : X×(α → m X) → m (Z×(α → m Z)))
  : X×(α → m X) → m ((Y×Z)×(α → m (Y×Z)))
  :=
  λ xdx => do
    let (y,dy) ← f xdx
    let (z,dz) ← g xdx
    let dy' : α → m (Y×Z) := λ a => do pure (← dy a, 0)
    let dz' : α → m (Y×Z) := λ a => do pure (0, ← dz a)
    let dyz : α → m (Y×Z) :=
      λ a => do 
        let dy ← dy a
        let dz ← dz a
        pure (dy, dz)
    pure ((y, z), dyz)

def fmaprFDM  {X Y Z : Type} [Vec X] [Vec Y] [Vec Z] {α : Type} {m} [VecMonad m] 
  (Tf : X×(α → X) → Y×(α → Y)) (Tg : X×(α → m X) → m (Z×(α → m Z)))
  : X×(α → m X) → m ((Y×Z)×(α → m (Y×Z)))
  := λ xdx => do
  let (y,dy) := Tf sorry
  let (z,dz) ← Tg xdx
  pure ((y, z), sorry)

def fmaprlFDM {Y Z} [Vec Y] [Vec Z] {α : Type} {m} [VecMonad m] 
  (f : X×(α → m X) → m (Y×(α → m Y))) 
  (g : X×(α → m X) → m (Z×(α → m Z)))
  : X×(α → m X) → m ((Y×Z)×(α → m (Y×Z)))
  :=
  λ xdx => do
    let (z,dz) ← g xdx
    let (y,dy) ← f xdx
    let dy' : α → m (Y×Z) := λ a => do pure (← dy a, 0)
    let dz' : α → m (Y×Z) := λ a => do pure (0, ← dz a)
    pure ((y, z), dy' + dz')

def uncurryM {X Y Z} {m} [VecMonad m] 
  (f : X → m (Y → m Z)) : X × Y → m Z
  := 
  λ (x, y) => do (← f x) y

class IgnoreEffect (m : Type u → Type v) [Monad m] where
  ignoreEffect {α} : m α → m α

  bind_ignore_effect {α β} (ma : m α) (mb : m β) : 
    (bind (ignoreEffect ma) λ _ => mb) = mb

export IgnoreEffect (ignoreEffect)

instance {σ} : IgnoreEffect (StateM σ) where
  ignoreEffect f := λ s => ((f s).1, s)
  bind_ignore_effect mb mb := by simp[bind, StateT.bind, pure]

def uncurryFDM {X Y Z} [Vec X] [Vec Y] [Vec Z] {α : Type} {m} [VecMonad m] [IgnoreEffect m]
  (Tf : X×(α → m X) → m ((Y → m Z) × (α → m (Y → m Z))))
  (Tfx : X → (Y × (α → m Y)) → m (Z × (α → m Z)))
  : (X×Y) × (α → m (X×Y)) → m (Z × (α → m Z))
  :=
  λ ((x,y), dxy) => do
    let xdx : X×(α → m X) := (x, λ a => do pure (← (dxy a)).1)
    let ydy : Y×(α → m Y) := (y, λ a => do pure (← dxy a).2)
    let (fx, df') ← Tf xdx
    let (z,  dfx) ← Tfx x ydy
    let df : α → Y → m Z := λ a y => do ((← (df' a)) y)
    pure (z, λ a => do (df a y + dfx a))

-- Caw we formulate it this way?
-- def uncurryFDM {X Y Z} [Vec X] [Vec Y] [Vec Z] {α : Type} {m} [VecMonad m] 
--   (Tf : X×(α → X) → ((Y → m Z) × (α → (Y → m Z))))
--   (Tfx : X → (Y × (α → m Y)) → m (Z × (α → m Z)))
--   : (X×Y) × (α → m (X×Y)) → m (Z × (α → m Z)) 

-- This probably relates to the following:

-- This is probably impossible
-- def pureFD {α X : Type} {m} [Monad m] : ((X × (α → X)) → Y × (α → Y)) → (X × (α → m X)) → m (Y × (α → m Y)) :=
--   λ f (x,dx) => do
--     sorry
    -- let xdx
    -- pure (f x, λ a => do pure (dx a))

abbrev FD (α : Type _) (X : Type) : Type := X×(α → X)

class IsMorFD {α X Y} (f : FD α X → FD α Y) where
  isFD : ∀ x dx dx', (f (x,dx)).1 = (f (x,dx')).1

instance fwdDiff_isMorFD {α X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f]
  : IsMorFD (fwdDiff α f) := by constructor; simp[fwdDiff]; done

abbrev FDM (α : Type _) (m : Type → Type) (X : Type) : Type := X×(α → m X)
  
class FwdDiffMonad (m : Type → Type) extends VecMonad m, IgnoreEffect m where
  IsSmoothM {X} [Vec X] (mx : m X) : Prop
  
  fwdDiffM {X Y} [Vec X] [Vec Y] (α : Type _) (f : X → m Y) : FDM α m X → m (FDM α m Y)

  fwdDiffM_id {X α} [Vec X] : fwdDiffM α (λ x : X => pure x) = λ xdx => pure xdx

  fwdDiffM_comp {X Y Z} [Vec X] [Vec Y] [Vec Z] 
    (f : Y → m Z) [IsSmooth f] (hf₂ : ∀ y, IsSmoothM (f y))
    (g : X → m Y) [IsSmooth g] (hf₂ : ∀ x, IsSmoothM (g x))
    : fwdDiffM α (λ (x : X) => pure x >>= g >>= f) 
      = 
      λ xdx => pure xdx >>= fwdDiffM α g >>= fwdDiffM α f

  mapFDM {X Y α} [Vec X] [Vec Y] (f : FD α X → FD α Y) : FDM α m X → m (FDM α m Y)

  mapFDM_id {X α} [Vec X]
    : mapFDM (id : FD α X → FD α X) 
      = 
      λ x => pure x

  mapFDM_comp {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : FD α Y → FD α Z) (g : FD α X → FD α Y) [IsMorFD f] [IsMorFD g]
    : mapFDM (λ x => x |> g |> f) 
      = 
      λ x => pure x >>= mapFDM g >>= mapFDM f

  fwdDiff_fwdDiffM {X Y α} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f] : fwdDiffM α (λ x => pure (f x)) = mapFDM (fwdDiff α f)

  uncurryD {X Y Z} [Vec X] [Vec Y] [Vec Z] (α : Type)
  (Tf : X×(α → m X) → m ((Y → m Z) × (α → m (Y → m Z))))
  (Tfx : X → (Y × (α → m Y)) → m (Z × (α → m Z)))
  : (X×Y) × (α → m (X×Y)) → m (Z × (α → m Z))

  curry_fwdDiff {α X Y Z} [Vec X] [Vec Y] [Vec Z] 
    (f : X → Y → m Z) [IsSmooth f] [∀ x, IsSmooth (f x)] (mhf₃ : ∀ x y, IsSmoothM (f x y))
    : fwdDiffM α (λ (x,y) => f x y) = uncurryD α (mapFDM (fwdDiff α f)) (λ x => fwdDiffM α (f x))

  -- pureFD {X Y} [Vec X] [Vec Y] {α : Type _} (Tf : X×(α → X) → Y×(α → Y)) : X×(α → m X) → Y×(α → m Y)

  -- pure_fwdDiffM {X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f]
  --   : fwdDiffM α (λ x : X => pure (f x)) 
  --     = 
  --     pure ∘ pureFD (fwdDiff α f)
  --     -- λ (x,dx) => pure (f x, λ a => do pure (δ f x (← dx a)))

  -- id_fwdDiffM {X} [Vec X] : fwdDiffM α (pure : X → m X) = pure


  -- comp_fwdDiffM {X Y Z} [Vec X] [Vec Y] [Vec Z] 
  --   (f : Y → m Z) [IsSmooth f] (hf₂ : ∀ y, IsSmoothM (f y))
  --   (g : X → m Y) [IsSmooth g] (hf₂ : ∀ x, IsSmoothM (g x))
  --   : fwdDiffM α (λ x => do f (← g x)) = λ xdx => do fwdDiffM α f (← fwdDiffM α g xdx)

  -- fmaplrM_fwdDiffM {X Y Z} [Vec X] [Vec Y] [Vec Z]
  --   (f : X → m Y) [IsSmooth f] (hf₂ : ∀ x, IsSmoothM (f x))
  --   (g : X → m Z) [IsSmooth g] (hg₂ : ∀ x, IsSmoothM (g x))
  --   : fwdDiffM α (fmaplrM f g) = fmaplrFDM (fwdDiffM α f) (fwdDiffM α g)

  -- uncurryM_fwdDiffM {X Y Z} [Vec X] [Vec Y] [Vec Z]
  --   (f : X → Y → m Z) [IsSmooth f] [∀ x, IsSmooth (f x)] (hf₃ : ∀ x y, IsSmoothM (f x y))
  --   : fwdDiffM α (uncurryM λ x => pure (f x)) 
  --     = 
  --     uncurryFDM (fwdDiffM α λ x => pure (f x)) (λ x => fwdDiffM α (f x))

  -- scomb_fwdDiffM {X Y Z} [Vec X] [Vec Y] [Vec Z] 
  --   (f : X → Y → m Z) [IsSmooth f] [∀ x, IsSmooth (f x)] (hf₃ : ∀ x y, IsSmoothM (f x y))
  --   (g : X → m Y) [IsSmooth g] (hf₂ : ∀ x, IsSmoothM (g x))
  --   : fwdDiffM α (λ x => do let y ← g x; f x y)
  --     = 
  --     λ xdx => do
  --       let Tidg := fmaplrFDM pure (fwdDiffM α g)
  --       let Tf   := fwdDiffM α (λ x => pure (f x))
  --       let Tfx  := λ x => fwdDiffM α (f x)
  --       let Tuncurryf := uncurryFDM Tf Tfx
  --       Tuncurryf (← Tidg xdx)


-- set_option pp.all true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
-- set_option trace.Meta.Tactic.simp.discharge true in

@[addPush]
theorem add_push_lin {X Y} [Vec X] [Vec Y] (f : X → Y) [IsLin f] (x x' : X)
  : f x + f x' = f (x + x') := sorry

@[addPull]
theorem add_pull_differential {X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f] (x dx dx' : X)
  : δ f x (dx + dx') = δ f x dx + δ f x dx' := sorry

@[addPull]
theorem add_pull_prod_fst {X Y} [Add X] [Add Y] (xy xy' : X×Y)
  : (xy + xy').1 = xy.1 + xy'.1 := sorry

@[addPull]
theorem add_pull_prod_snd {X Y} [Add X] [Add Y] (xy xy' : X×Y)
  : (xy + xy').2 = xy.2 + xy'.2 := sorry

noncomputable
instance {σ} [Vec σ] : FwdDiffMonad (StateM σ) where
  IsSmoothM mx := IsSmooth (λ s => mx s)
  
  fwdDiffM α f := λ (x,adx) s => (((f x s).1, λ a ds => δ f x (adx a ds).1 s + δ (f x) s (adx a ds).2), (f x s).2)

  fwdDiffM_id := by simp[pure,StateT.pure,StateM,StateT,Id,prod_add_elemwise]

  fwdDiffM_comp f hf₁ mhf₂ g hg₁ mhg₂ := by
    simp[pureZero, pure,StateT.pure,bind,StateT.bind,StateT,StateM,Id,prod_add_elemwise,uncurryFDM,fmaplrFDM] at f hf₁ mhf₂ g hg₁ mhg₂ ⊢
    funext xdx s; simp
    funext a ds; simp
    have hg₂ : ∀ x, IsSmooth (g x) := λ x => (mhg₂ x)
    have hf₂ : ∀ y, IsSmooth (f y) := λ y => (mhf₂ y)
    simp[addPull]
    have h : ∀ {X} [Vec X] (a b c d : X), a + b + (c + d) = a + c + (b + d) := sorry;
    constructor {rw[h]} {rw[h]}
    done

  mapFDM Tf := λ (x,dx) s => (((Tf (x, default)).1, λ a ds => ((Tf (x, λ a' => (dx a' ds).1)).2 a, (dx a ds).2)),s)

  mapFDM_id := by simp[pure,StateT.pure]

  mapFDM_comp Tf Tg hf hg := by 
    simp[bind,StateT.bind,pure,StateT.pure]
    funext xdx s; simp
    constructor
    { rw[hf.isFD _ default (Tg (xdx.fst, default)).snd] }
    { funext a ds; simp 
      rw[hg.isFD _ default fun a' => (Prod.snd xdx a' ds).fst] }

  fwdDiff_fwdDiffM f _ := by 
    simp[fwdDiff,pure,StateT.pure,StateT,StateM,Id,prod_add_elemwise]

  uncurryD α Tf Tfx := λ ((x,y), dxy) s => 
    let xdx := (x, λ a ds => ((dxy a ds).1.1,(dxy a ds).2))
    let ydy := (y, λ a ds => ((dxy a ds).1.2,(dxy a ds).2))
    let ((fx, df'),s) := Tf xdx s
    let df : α → StateM σ _ := λ a (ds : σ) => (df' a ds).1 y s -- This is an odd operations
    let ((z,  dfx),s) := Tfx x ydy s
    ((z, df + dfx), s)

  curry_fwdDiff f hf₁ hf₂ mhf₃ := by 
    simp[uncurryFDM,bind,StateT.bind,pure,StateT.pure,StateM,StateT,Id,fwdDiff,pureZero] at f hf₁ hf₂ mhf₃ ⊢
    funext x s; simp
    funext a ds; simp
    have h : ∀ {X} [Vec X] (a b c : X), a + b + c = a + (b + c) := sorry;
    rw[h];

    

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
