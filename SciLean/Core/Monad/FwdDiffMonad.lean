import SciLean.Core.Monad.VecMonad

namespace SciLean

noncomputable
def fwdDiff' {α : Type _} {X Y} [Vec X] [Vec Y] (f : X → Y) : (X × (α → X)) → (Y × (α → Y)) :=
  λ (x,dx) => (f x, λ a => δ f x (dx a))

@[simp]
theorem comp.arg_x.fwdDiff'_simp {α : Type _} {X Y Z} [Vec X] [Vec Y] [Vec Z]
  (f : Y → Z) [IsSmooth f]
  (g : X → Y) [IsSmooth g]
  : (fwdDiff' (α:=α) λ x => f (g x)) = (λ xdx => fwdDiff' f (fwdDiff' g xdx)) := by simp[fwdDiff']

/- Currently we assume that it is also vector monad as we do not have manifolds/diffeological spaces
  -/
class FwdDiffMonad (m : Type → Type) extends VecMonad m where
  IsSmoothM {X} [Vec X] (mx : m X) : Prop
  
  fwdDiffM {α : Type _} {X Y} [Vec X] [Vec Y] (f : X → m Y) : (X × (α → m X)) → m (Y × (α → m Y))

  -- pairFDM {α : Type _} {X Y} [Vec X] [Vec Y] (xdx : X × (α → m X)) (mydy : m (Y × (α → m Y)))
  --   : m ((X×Y) × (α → m (X×Y)))

  -- diffM {X} [Vec X] (mx : m X) : m (X × m X)

  -- This is incorrect!
  -- fwdDiffM_diffM {α : Type _} {X Y} [Vec X] [Vec Y] (f : X → m Y) [IsSmooth f] (hf : ∀ x, IsSmoothM (f x))
  --   : fwdDiffM (α:=α) f = λ (x,dx) => do
  --     let (y, dfds) ← diffM (f x)
  --     let df : α → m Y := λ a => do 
  --       let dfdx := δ f x (← dx a)
  --       dfdx + dfds
  --     pure (y, df) 

  -- pureFwdDiffM {X Y : Type} : (Y × (X → Y)) → m (Y × (X → m Y))
  -- bindFwdDiffM {α : Type _} {X Y : Type} [Vec X] [Vec Y] : m (X × (α → m X)) → ((X × (α → X)) → m (Y × (α → m Y))) → m (Y × (α → m Y))

  -- pureFwdDiffM_fst {X Y Z} (f : Y → m Z) (xdx : Y × (X → Y)) : bind (pureFwdDiffM xdx) (λ x => f x.1) = f xdx.1
  -- pureFwdDiffM_snd {X Y Z} (f : (X → m Y) → m Z) (xdx : Y × (X → Y)) : bind (pureFwdDiffM xdx) (λ x => f x.2) = f (λ x => pure (xdx.2 x))

  fwdDiffM_pure {α : Type _} {X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f]
    : fwdDiffM (α:=α) (λ x => pure (f x)) 
      = 
      λ (x,dx) => pure (f x, λ a => do pure (δ f x (← dx a)))
  fwdDiffM_comp {α : Type _} {X Y Z} [Vec X] [Vec Y] [Vec Z]
    (f : Y → m Z) [IsSmooth f] (hf : ∀ x, IsSmoothM (f x))
    (g : X → m Y) [IsSmooth g] (hg : ∀ x, IsSmoothM (g x))
    : fwdDiffM (α:=α) (λ x => g x >>= f) 
      = 
      λ x => fwdDiffM g x >>= fwdDiffM f

  -- revDiffM {α : Type _} {X Y} [Vec X] [Vec Y] (f : X → m Y) : (X × (X → m α)) → m (Y × (Y → m α))
  -- revDiffM_comp {α : Type _} {X Y Z} [Vec X] [Vec Y] [Vec Z]
  --   (f : Y → m Z) [IsSmooth f] (hf : ∀ x, IsSmoothM (f x))
  --   (g : X → m Y) [IsSmooth g] (hg : ∀ x, IsSmoothM (g x))
  --   : revDiffM (α:=α) (λ x => g x >>= f) = λ x => revDiffM g x >>= revDiffM f

  -- to and from Forward Differentiable Monad
  -- toFDM   {α : Type _} {X} (xdx : (m X) × (α → m X)) : m (X × (α → m X))
  -- fromFDM {α : Type _} {X} (xdx : m (X × (α → m X))) : (m X) × (α → m X)

  -- the reverse does not hold
  -- from_to_fdm {α : Type _} {X} (xdx : (m X) × (α → m X)) : fromFDM (toFDM xdx) = xdx

  -- bind_fwdDiff'_fwdDiffM {α : Type _} {X Y} [Vec X] [Vec Y]
  --   (f : X → m Y) [IsSmooth f] (hmf : ∀ x, IsSmoothM (f x))
  --   : fwdDiff' (bind · f) 
  --     = 
  --     λ (xdx : (m X) × (α → m X)) => 
  --     let fdx := fwdDiffM (α := α) f
  --     fromFDM (bind (toFDM xdx) fdx)

  -- fwdDiffM_bind {α : Type _} {X Y} [Vec X] [Vec Y] 
  --   (f : X → m Y) [IsSmooth f] (hmf : ∀ x, IsSmoothM (f x))
  --   : fwdDiffM (α := α) f 
  --     =   
  --     let df := fwdDiff' (α := α) (bind · f)
  --     toFDM ∘ df ∘ fromFDM ∘ pure

  -- liftChange {X} [Vec X] : m X → m (m' X)

  -- This is unique to vector monads and will dissappear with manifolds
  -- pureM {X} [Vec X] : m X → m' X
  -- toDiffM   {X} [Vec X] : (mx : m X)   → (ds : m Unit) → m' X
  -- fromDiffM {X} [Vec X] : (mdx : m' X) → (ds : m Unit) → m X

  -- pure_diffM_simp {X} [Vec X] : diffM (pure : X → m X) = λ (x : X) => liftChange (pure (λ dx => dx))
  -- pure_fwdDiffM_simp {X} [Vec X] : diffM (pure : X → m X) = λ (x : X) => liftChange (pure (λ dx => dx))

  -- pure_arg_x_diff {X} [Vec X] : X → X → m X

  -- bind_arg_x_diff {X Y} [Vec X] [Vec Y] : (X → m Y) → m X → m X → m Y
  -- bind_arg_f_diff {Y} [Vec Y] : m X → (X → m Y) → (X → m Y) → m Y

  -- pure_diff_simp {X} [Vec X] : δ (pure : X → m X) = λ x dx => pureZero dx
  -- pure_diffM_simp {X} [Vec X] (x : X) : diffM (pure x) = pureM (pure 0)

  -- pure_isSmoothM {X} [Vec X] (x : X)
  --   : IsSmoothM (pure x)

  -- pure_arg_x_isSmooth {X} [Vec X]
  --   : IsSmooth (λ (x : X) => (pure x : m X))
  -- pure_arg_x_diff_simp {X} [Vec X]
  --   : δ (pure : X → m X) = pure_arg_x_diff

  -- bind_isSmoothM {X Y} [Vec X] [Vec Y] (f : X → m Y) [IsSmooth f] (hf : ∀ x, IsSmoothM (f x)) (mx : m X) (hmx : IsSmoothM mx)
  --   : IsSmoothM (bind mx f)
  
  -- bind_arg_x_isSmooth {X Y} [Vec X] [Vec Y] (f : X → m Y) [IsSmooth f] (hf : ∀ x, IsSmoothM (f x))
  --   : IsSmooth (λ mx => bind mx f)
  -- bind_arg_x_diff_simp {X Y} [Vec X] [Vec Y] (f : X → m Y) [IsSmooth f] (hf : ∀ x, IsSmoothM (f x))
  --   : δ (λ mx => bind mx f) = bind_arg_x_diff f 

  -- bind_arg_f_diff_isSmooth {Y} [Vec Y] (mx : m X)
  --   : IsSmooth (λ (f : X → m Y) => bind mx f)
  -- bind_arg_f_diff_simp {Y} [Vec Y] (mx : m X)
  --   : δ (bind mx) = λ (f df : X → m Y) => bind_arg_f_diff mx f df

  -- comp_diff_simp {X Y Z} [Vec X] [Vec Y] [Vec Z] 
  --   (f : Y → m Z) [IsSmooth f] (hmf : ∀ y, IsSmoothM (f y))
  --   (g : X → m Y) [IsSmooth g] (hmg : ∀ x, IsSmoothM (g x))
  --   : δ (λ (mx : m X) => do
  --       let x ← mx
  --       let y ← g x
  --       let z ← f y
  --       (pure z : m Z))
  --       = 
  --       λ (mx mdx : m X) => ((do 
  --       let xdx ← toFDM (mx, λ _ => mdx)
  --       let ydy ← fwdDiffM g xdx
  --       let zdz ← fwdDiffM f ydy
  --       zdz.2 ()) : m Z)

export FwdDiffMonad (fwdDiffM)

class IsSmoothM [FwdDiffMonad m] [Vec X] (mx : m X) where
  isSmoothM : FwdDiffMonad.IsSmoothM mx




section SmoothnessProperties

  variable [FwdDiffMonad m]
  variable {X Y Z} [Vec X] [Vec Y] [Vec Z]

  def pairFDM {α : Type _} {X Y} [Vec X] [Vec Y] (xdx : X × (α → m X)) (ydy : Y × (α → m Y))
    : (X×Y) × (α → m (X×Y))
  := 
    let (x,dx) := xdx
    let (y,dy) := ydy
    let dx' : α → m (X×Y) := λ a => do pureZero (← dx a, 0)
    let dy' : α → m (X×Y) := λ a => do pure (0, ← dy a)
    ((x,y), dx'+dy')

  instance (x : m X) [IsSmoothM x]
           (f : X → m Y) [IsSmooth f] [∀ x, IsSmoothM (f x)] : IsSmoothM (x >>= f) := sorry

  instance (f : X → m Y) [IsSmooth f] [∀ x, IsSmoothM (f x)] : IsSmooth (bind · f) := sorry

  instance (mx : m X) : IsSmooth (λ f => (bind mx f : m Y)) := sorry

  instance (g : X → m Y) [IsSmooth g] [∀ x, IsSmoothM (g x)] 
    (f : X → Y → m Z) [IsSmooth f] [∀ x, IsSmooth (f x)] [∀ x y, IsSmoothM (f x y)]
    : IsSmooth (λ x => 
    bind (g x) λ y => 
    f x y) := sorry

  -- instance (g : X → m Y) [IsSmooth g] [∀ x, IsSmoothM (g x)] 
  --   (f : X → Y → m Z) [IsSmooth f] [∀ x, IsSmooth (f x)] [∀ x y, IsSmoothM (f x y)]
  --   (xm : m X) [IsSmoothM mx]
  --   : IsSmoothM (
  --       bind mx λ x =>
  --       bind (g x) λ y =>
  --       f x y) := by infer_instance

  example (mx : m X) [IsSmoothM mx] (g : X → m Y) [IsSmooth g] [∀ x, IsSmoothM (g x)] 
    (f : X → Y → m Z) [IsSmooth f] [∀ x, IsSmooth (f x)] [∀ x y, IsSmoothM (f x y)]
    : IsSmoothM (
    bind mx λ x => 
    bind (g x) λ y => 
    f x y) := by infer_instance

  instance (x : X) : IsSmoothM (pure x : m X) := sorry
  instance : IsSmooth (pure : X → m X) := sorry

  example (f : Y → m Z) [IsSmooth f] [hf : ∀ x, IsSmoothM (f x)]
          (g : X → m Y) [IsSmooth g] [hg : ∀ x, IsSmoothM (g x)]
    : IsSmooth (λ x => g x >>= f) := by infer_instance

  example (f : Y → m Z) [IsSmooth f] [hf : ∀ x, IsSmoothM (f x)]
          (g : X → m Y) [IsSmooth g] [hg : ∀ x, IsSmoothM (g x)]
          (x : X)
    : IsSmoothM (g x >>= f) := by infer_instance

  set_option synthInstance.maxSize 2048
  set_option synthInstance.maxHeartbeats 500000
        
  example (f : X → m X) [IsSmooth f] [hf : ∀ x, IsSmoothM (f x)] 
          (g : X → X) [IsSmooth g]
          (x : X)
    : IsSmoothM ((do 
                  let a ← f (g x)
                  let b ← f (g a)
                  let c ← f (g b)
                  f c) : m X) := by infer_instance

  example (f : Y → m Z) [IsSmooth f] [hf : ∀ x, IsSmoothM (f x)]
          (g : X → m Y) [IsSmooth g] [hg : ∀ x, IsSmoothM (g x)]
          (mx : m X) [IsSmoothM mx]
    : IsSmoothM (mx >>= g >>= f) := by infer_instance

end SmoothnessProperties


section DifferentiationProperties

  variable [FwdDiffMonad m]
  variable {X Y Z} [Vec X] [Vec Y] [Vec Z]
  variable {α : Type _}

  -- @[simp]
  -- theorem fwdDiffM_bind
  --   (f : X → m Y) [IsSmooth f] [hf : ∀ x, IsSmoothM (f x)]
  --   : fwdDiffM (α := α) f 
  --     =   
  --     let df := fwdDiff' (α := α) (bind · f)
  --     toFDM ∘ df ∘ fromFDM ∘ pure
  --   := FwdDiffMonad.fwdDiffM_bind f (λ x => (hf x).1)

  -- @[simp]
  -- theorem bind.arg_f.fwdDiffM_simp {α : Type _} (f : X → Y) [IsSmooth f]
  --   : fwdDiffM (m:=m) (α:=α) (λ x => pure (f x)) 
  --     = 
  --     λ (x,dx) => pure (f x, λ a => do pure (δ f x (← dx a)))
  --   :=
  --    FwdDiffMonad.fwdDiffM_pure f


  @[simp]
  theorem pure.arg_x.fwdDiffM_simp {α : Type _} (f : X → Y) [IsSmooth f]
    : fwdDiffM (m:=m) (α:=α) (λ x => pure (f x)) 
      = 
      λ (x,dx) => pure (f x, λ a => do pure (δ f x (← dx a)))
    :=
     FwdDiffMonad.fwdDiffM_pure f

  @[simp]
  theorem compM.arg_x.fwdDiffM_simp_mix {α : Type _} (f : Y → m Z) [IsSmooth f] [∀ y, IsSmoothM (f y)]
    (g : X → Y) [IsSmooth g]
    : fwdDiffM (m:=m) (α:=α) (λ x => f (g x)) 
      = 
      λ (x,dx) => pure (g x, λ a => do pure (δ g x (← dx a))) >>= fwdDiffM f  
    := sorry
      
  @[simp]
  theorem compM.arg_x.fwdDiffM_simp
    (f : Y → m Z) [IsSmooth f] [hf : ∀ x, IsSmoothM (f x)]
    (g : X → m Y) [IsSmooth g] [hg : ∀ x, IsSmoothM (g x)]
    : fwdDiffM (α:=α) (λ x => g x >>= f)
      =
      (λ xdx => do
        let ydy ← fwdDiffM g xdx 
        fwdDiffM f ydy) := 
    FwdDiffMonad.fwdDiffM_comp f (λ x => (hf x).1) g (λ x => (hg x).1)

  theorem asdf {α : Type _}
    (g : X → m Y) [IsSmooth g] [∀ x, IsSmoothM (g x)]
    (f : X → Y → m Z) [IsSmooth f] [∀ x, IsSmooth (f x)] [∀ x y, IsSmoothM (f x y)]
    : 
      fwdDiffM (α:=α) (fun x => (do let y ← g x; f x y : m Z))
      =
      (λ xdx => do
        let ydy ← fwdDiffM g xdx
        fwdDiffM (λ ((x,y) : X×Y) => f x y) (pairFDM xdx ydy))
    := sorry


end DifferentiationProperties

  -- variable [FwdDiffMonad m]
  -- variable {X Y Z} [Vec X] [Vec Y] [Vec Z]
  
  -- theorem fwdDiffM_comp {α : Type _} {X Y Z} [Vec X] [Vec Y] [Vec Z] [FwdDiffMonad m]
  --   (f : Y → m Z) [IsSmooth f] [hf : ∀ x, IsSmoothM (f x)]
  --   (g : X → m Y) [IsSmooth g] [hg : ∀ x, IsSmoothM (g x)]
  --   : fwdDiffM (α:=α) (λ x => g x >>= f) 
  --     = 
  --     λ x => fwdDiffM g x >>= fwdDiffM f := by 

  --   simp[FwdDiffMonad.fwdDiffM_bind ]
  --   sorry


def DStateM σ α := σ → (σ → α × σ) × α × σ

instance {σ} : Monad (DStateM σ) where
  pure a := λ s => (λ ds => (a, ds), a, s)
  bind mx f := λ s => 
    let (dx, x, s) := mx s
    let (df, fx, s) := f x s
    (λ ds => df (dx ds).2, fx, s)

-- set_option synthInstance.maxSize 2048
-- set_option synthInstance.maxHeartbeats 500000

-- set_option pp.all true in
-- set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.simp.unify true in
-- set_option trace.Meta.synthInstance true in
noncomputable
instance StateM.instManifoldMonad {σ} [Vec σ] : FwdDiffMonad (StateM σ) where
  IsSmoothM mx := IsSmooth mx

  -- diffM f := λ x s => (λ dx ds => δ f x dx s + δ (f x) ds s, (f x s).2)
  fwdDiffM f := λ (x,adx) s => (((f x s).1, λ a ds => δ f x (adx a ds).1 s + δ (f x) s (adx a ds).2), (f x s).2)

  -- diffM mx := λ s =>
  --   let (x, s) := mx s
  --   ((x, λ ds => δ mx s ds), s)

  -- fwdDiffM_diffM f sf hf := by
  --   have ihf : ∀ y, IsSmooth (f y) := hf
  --   simp[pure, StateT.pure, bind, StateT.bind, StateM, StateT, Id]
  --   simp[pure, StateT.pure, bind, StateT.bind, StateM, StateT, Id] at f ihf sf
  --   funext x s
  --   simp
  --   funext a ds
  --   admit

  -- pureFwdDiffM {X Y : Type} 
  --   := λ (x,dx) => 
  --       pure (x, λ a => pure (dx a))

  -- bindFwdDiffM := λ xdx f => do
  --   let (x,dx) ← xdx
  --   let y ← (f (x,sorry)).1
  --   let dy ← (f x).2
  --   let dx' := sorry
  --   f (x,dx')
    --{α : Type _} {X Y : Type} [Vec X] [Vec Y] : m (X × (α → m X)) → ((X × (α → X)) → m (Y × (α → m Y))) → m (Y × (α → m Y))

  -- pureFwdDiffM_fst {X Y Z} (f : Y → m Z) (xdx : Y × (X → Y)) : bind (pureFwdDiffM xdx) (λ x => f x.1) = f xdx.1
  -- pureFwdDiffM_snd {X Y Z} (f : (X → m Y) → m Z) (xdx : Y × (X → Y)) : bind (pureFwdDiffM xdx) (λ x => f x.2) = f (λ x => pure (xdx.2 x))

  fwdDiffM_pure f _ := by simp[pure, StateT.pure, bind, StateT.bind, StateM, StateT, Id]; simp[prod_add_elemwise]; done
  fwdDiffM_comp f sf hf g sg hg := by
    have ihf : ∀ y, IsSmooth (f y) := hf
    have ihg : ∀ x, IsSmooth (g x) := hg
    simp[pure, StateT.pure, bind, StateT.bind, StateM, StateT, Id] at f g ihf ihg sf sg ⊢
    -- simp[pure, StateT.pure, bind, StateT.bind, StateM, StateT, Id] at f g ihf ihg sf sg
    funext x s
    simp
    funext a ds
    have hh1 : ∀ s : σ, IsSmooth (λ x => (g x s).1) := by infer_instance
    have hh2 : ∀ s : σ, IsSmooth (λ x => (g x s).2) := by infer_instance
    simp
    admit -- almost done


def StateT.runFwdDiff {σ X} [Vec σ] [Vec X] (mdx : (Unit×(Unit → StateM σ Unit)) → StateM σ (X × (Unit → StateM σ X))) (s ds : σ) : X×σ :=
  (mdx ((),λ _ ds' => ((),ds')) s).1.2 () ds

@[simp ↓ high]
theorem StateM.run.diff_simp {σ X} [Vec σ] [Vec X] (mx : StateT σ Id X) [IsSmoothM mx] 
  : δ mx.run = λ (s ds : σ) => 
      StateT.runFwdDiff (fwdDiffM (α:=Unit) (λ _ => mx)) s ds
  := by simp[StateT.runFwdDiff, StateT.run, fwdDiffM, StateM, StateT, Id]

instance StateM.run.isSmooth {σ X} [Vec σ] [Vec X] (mx : StateT σ Id X) [inst : IsSmoothM mx] : IsSmooth (mx.run) := 
by 
  simp[StateT.run]; simp[StateM, StateT, Id, IsSmoothM] at mx inst; admit -- infer_instance

instance {σ} [Vec σ] : IsSmoothM (get : StateM σ σ) := sorry

@[simp]
theorem StateT.get.fwdDiffM {α : Type _} {X σ} [Vec X] [Vec σ] : fwdDiffM (α:=α) (λ x : X => (get : StateT σ Id σ)) = λ xdx s => ((s, λ a ds => let ds' := (xdx.2 a ds).2; (ds', ds')), s) := 
by
  unfold fwdDiffM
  unfold StateM.instManifoldMonad
  simp[StateT.get, StateT, StateM, Id, get, getThe, MonadStateOf.get]
  funext xdx s
  simp[prod_add_elemwise]
  done

#eval StateT.run (m:=Id) (do
  let x ← get
  let y ← pure (x * x)
  let z ← pure (y + y)
  pure z)
  (2.0 : ℝ)

variable (f : ℝ → StateM ℝ ℝ) [IsSmooth f] [∀ x, IsSmoothM (f x)]

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 500000

set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.rewrite true in
example : δ (λ x : ℝ => StateT.run (m:=Id) (do
  let x ← get
  let y ← f (x * x)
  let z ← f (y * y)
  -- let b ← f (z * z)
  -- let a ← f (z + b)
  pure y
  ) x)
   = 0 
:= by 
  simp only [StateM.run.diff_simp]  -- This is odd ...
  simp
  conv =>
    lhs
    enter [s,ds,1,xdx,2,ydy,2,ydy]
    simp
  simp only [SciLean.compM.arg_x.fwdDiffM_simp]

#check Nat

@[simp ↓ low-2, simp_diff low-2]
theorem diff_of_scomb {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
  (f : X → Y → Z) [IsSmooth f] [∀ y, IsSmooth (f y)]
  (g : X → Y) [IsSmooth g]
  : δ (λ x => f x (g x)) 
    = 
    λ x dx => δ f x dx (g x) + 
              δ (f x) (g x) (δ g x dx) := sorry


set_option trace.Meta.Tactic.simp.discharge true in
@[simp]
example {α : Type _} {X Y Z σ} [Vec X] [Vec Y] [Vec Z] [Vec σ]
  (g : X → StateM σ Y) [hg1 : IsSmooth g] [hg2m : ∀ x, IsSmoothM (g x)]
  (f : X → Y → StateM σ Z) [hf1 : IsSmooth f] [hf2 : ∀ x, IsSmooth (f x)] [hf3m : ∀ x y, IsSmoothM (f x y)]
  : 
    fwdDiffM (α:=α) (fun x => (do let y ← g x; f x y : StateM σ Z))
    =
    (λ xdx => do
      let ydy ← fwdDiffM g xdx
      fwdDiffM (λ ((x,y) : X×Y) => f x y) (pairFDM xdx ydy))
  := by
  simp[StateT, StateM, Id, StateT.bind, bind, fwdDiffM, pairFDM, pure, StateT.pure, pureZero] at f g hf1 hf2 hg1 ⊢
  have hh1 : ∀ s : σ, IsSmooth (λ x => (g x s).1) := by infer_instance
  have hh2 : ∀ s : σ, IsSmooth (λ x => (g x s).2) := by infer_instance
  have hg2 : ∀ x, IsSmooth (g x) := λ x => (hg2m x).1
  have hf3 : ∀ x y, IsSmooth (f x y) := λ x y => (hf3m x y).1
  simp
  funext x s
  simp
  funext a ds
  simp
  simp[prod_add_elemwise]
  -- simp[fwdDiffM,bind,StateT.bind,pairFDM]



example (f : ℝ → StateM ℝ ℝ) [IsSmooth f] [∀ x, IsSmoothM (f x)] 
  : IsSmoothM ((do
  let x ← get
  let y ← f (x * x)
  let z ← f (x + x * y)
  f (x + y + z)) : StateM ℝ ℝ) := by infer_instance

example (f : ℝ → StateM ℝ ℝ) [IsSmooth f] [∀ x, IsSmoothM (f x)] 
  : IsSmoothM ((do
  bind get λ x => 
  bind get λ y => 
  bind get λ z =>
  f x) : StateM ℝ ℝ) := by infer_instance

example : IsSmoothM ((do
  let x ← get
  let y ← f (x * x)
  pure y) : StateM ℝ ℝ) := by infer_instance


example : IsSmooth ((do
  let x ← get
  let y ← f (x * x)
  pure y) : StateM ℝ ℝ).run := by infer_instance
