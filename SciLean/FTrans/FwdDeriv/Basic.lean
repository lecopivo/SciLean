import SciLean.FTrans.FDeriv.Basic
import SciLean.Profile

namespace SciLean

/-- `BroadcastType tag X ι MX` says that `MX` is `ι`-many copies of `X`

  `tag` is used to indicate the class of broadcasting types. For example, dense or sparse matrices are broadcast type for vectors.
  -/
class BroadcastType (tag : Name) (R : Type _) [Ring R] (ι : Type _) (X : Type _) (MX : outParam $ Type _) [AddCommGroup X] [Module R X] [AddCommGroup MX] [Module R MX] where
  equiv  : MX ≃ₗ[R] (ι → X)




variable 
  {R : Type _} [Ring R]
  {X : Type _} [AddCommGroup X] [Module R X]
  {Y : Type _} [AddCommGroup Y] [Module R Y]
  {MX : Type _} [AddCommGroup MX] [Module R MX]
  {MY : Type _} [AddCommGroup MY] [Module R MY]
  {ι : Type _} -- [Fintype ι]
  {κ : Type _} -- [Fintype κ]
  {E ME : κ → Type _} 
  [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
  [∀ j, AddCommGroup (ME j)] [∀ j, Module R (ME j)]


def broadcast (tag : Name) [BroadcastType tag R ι X MX] [BroadcastType tag R ι Y MY] 
 (f : X → Y) : MX → MY := fun mx =>
  (BroadcastType.equiv tag (R:=R)).invFun fun (i : ι) => f ((BroadcastType.equiv tag (R:=R)) mx i)

 
open BroadcastType in
instance [BroadcastType tag R ι X MX] [BroadcastType tag R ι Y MY] : BroadcastType tag R ι (X×Y) (MX×MY) where
  equiv := {
    toFun  := fun (mx,my) i => (equiv tag (R:=R) mx i, 
                                equiv tag (R:=R) my i)
    invFun := fun xy => ((equiv tag (R:=R)).invFun fun i => (xy i).1, 
                         (equiv tag (R:=R)).invFun fun i => (xy i).2) 
    map_add'  := by intro x y; funext i; simp
    map_smul' := by intro x y; funext i; simp
    left_inv  := fun _ => by simp
    right_inv := fun _ => by simp
  }

open BroadcastType in
instance [∀ j, BroadcastType tag R ι (E j) (ME j)]
  : BroadcastType tag R ι (∀ j, E j) (∀ j, ME j) where
  equiv := {
    toFun  := fun mx i j => equiv tag (R:=R) (mx j) i 
    invFun := fun x j => (equiv tag (R:=R)).invFun (fun i => x i j)
    map_add'  := by intro x y; funext i j; simp
    map_smul' := by intro x y; funext i j; simp
    left_inv  := fun _ => by simp
    right_inv := fun _ => by simp
  }

open BroadcastType in
instance : BroadcastType `normal R Unit X X where
  equiv := {
    toFun  := fun x _ => x
    invFun := fun x => x ()
    map_add'  := by intro x y; funext _; simp
    map_smul' := by intro x y; funext _; simp
    left_inv  := fun _ => by simp
    right_inv := fun _ => by simp
  }

-- open BroadcastType in
-- instance [BroadcastType `normal R (Fin n) X MX] : BroadcastType `normal R (Fin (n+1)) X (X×MX) where
--   equiv := {
--     toFun  := fun (x,mx) i =>
--       match i with
--       | ⟨0, _⟩ => x
--       | ⟨i'+1, h⟩ => 
--         let i' : Fin n := ⟨i', by aesop⟩
--         equiv `normal (R:=R) mx i'
--     invFun := fun x => (x 0, (equiv `normal (R:=R)).invFun fun i : Fin n => x ⟨i.1+1, by aesop⟩)
--     map_add'  := by intro x y; funext ⟨i,hi⟩; induction i; simp; rfl; simp
--     map_smul' := by intro x y; funext ⟨i,hi⟩; induction i; simp; rfl; simp
--     left_inv  := fun (x,mx) => by simp; rfl
--     right_inv := fun _ => by simp; funext ⟨i,hi⟩; induction i; simp; rfl
--   }


-- instance : Broadcast `EigenSparse ℝ^m (Eigen.SparseMatrix n m) (Fin n) where
-- instance : Broadcast `EigenDense ℝ^m (Eigen.Matrix n m) (Fin n) where


noncomputable
def fwdDeriv
  (K : Type _) [NontriviallyNormedField K]
  (tag : Name) (ι : Type _)
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {DX : Type _} [AddCommGroup DX] [Module K DX]
  {DY : Type _} [AddCommGroup DY] [Module K DY]
  [BroadcastType tag K ι X DX] [BroadcastType tag K ι Y DY]
  (f : X → Y) (x : X) (dx : DX) : Y×DY :=
  (f x, broadcast tag (R:=K) (ι:=ι) (fun dx => fderiv K f x dx) dx)

namespace fwdDeriv

variable
  {K : Type _} [NontriviallyNormedField K]
  {tag : Name} {ι : Type _}
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]
  {DX : Type _} [AddCommGroup DX] [Module K DX] [BroadcastType tag K ι X DX]
  {DY : Type _} [AddCommGroup DY] [Module K DY] [BroadcastType tag K ι Y DY]
  {DZ : Type _} [AddCommGroup DZ] [Module K DZ] [BroadcastType tag K ι Z DZ]
  {κ : Type _} [Fintype κ]
  {E : κ → Type _} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace K (E j)]
  {DE : κ → Type _} [∀ j, AddCommGroup (DE j)] [∀ j, Module K (DE j)]
  [∀ j, BroadcastType tag K ι (E j) (DE j)]
  

theorem id_rule 
  : fwdDeriv K tag ι (fun x : X => x) = fun x dx => (x,dx) :=
by
  unfold fwdDeriv; unfold broadcast
  simp

theorem const_rule (x :X)
  : fwdDeriv K tag ι (fun y : Y => x) = fun y dy => (x, 0) :=
by
  unfold fwdDeriv; unfold broadcast
  funext y dy
  simp; rfl

theorem comp_rule 
  (g : X → Y) (hg : Differentiable K g)
  (f : Y → Z) (hf : Differentiable K f)
  : fwdDeriv K tag ι (fun x : X => f (g x)) 
    = 
    fun x dx => 
      let ydy := fwdDeriv K tag ι g x dx 
      let zdz := fwdDeriv K tag ι f ydy.1 ydy.2 
      zdz :=
by
  unfold fwdDeriv; unfold broadcast
  funext x dx; congr; funext i;
  rw[fderiv.comp_rule g hg f hf]
  simp


theorem let_rule 
  (g : X → Y) (hg : Differentiable K g)
  (f : X → Y → Z) (hf : Differentiable K (fun (xy : X×Y) => f xy.1 xy.2))
  : fwdDeriv K tag ι (fun x : X => let y := g x; f x y) 
    = 
    fun x dx => 
      let ydy := fwdDeriv K tag ι g x dx 
      let zdz := fwdDeriv K tag ι (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz :=
by
  unfold fwdDeriv; unfold broadcast
  funext x dx; congr; funext i
  rw[fderiv.let_rule g hg f hf]; 
  simp; congr; simp



theorem pi_rule
  (f : (j : κ) → X → E j) (hf : ∀ j, Differentiable K (f j))
  : (fwdDeriv K tag ι fun (x : X) (j : κ) => f j x)
    = 
    fun x dx =>
      (fun j => f j x, fun j => (fwdDeriv K tag ι (f j) x dx).2) := 
by 
  unfold fwdDeriv; unfold broadcast
  funext x; rw[fderiv_pi (fun i => hf i x)]
  simp; funext dx; simp[BroadcastType.equiv]


-- Register `fwdDeriv` as function transformation ------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq

def fwdDeriv.discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `fwdDeriv_discharger (fun _ => return s!"discharge {← ppExpr e}") do
  let cache := (← get).cache
  let config : FProp.Config := {}
  let state  : FProp.State := { cache := cache }
  let (proof?, state) ← FProp.fprop e |>.run config |>.run state
  modify (fun simpState => { simpState with cache := state.cache })
  return proof?

open Lean Elab Term FTrans
def fwdDeriv.ftransExt : FTransExt where
  ftransName := ``fwdDeriv

  getFTransFun? e := 
    if e.isAppOf ``fwdDeriv then

      if let .some f := e.getArg? 19 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``fwdDeriv then
      e.modifyArg (fun _ => f) 19
    else          
      e

  identityRule     := .some <| .thm ``id_rule
  constantRule     := .some <| .thm ``const_rule
  compRule         := .some <| .thm ``comp_rule
  lambdaLetRule    := .some <| .thm ``let_rule
  lambdaLambdaRule := .some <| .thm ``pi_rule

  discharger := fwdDeriv.discharger


-- register fderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``fwdDeriv, fwdDeriv.ftransExt))


example : BroadcastType tag K ι X DX := by infer_instance


@[ftrans_rule]
theorem HAdd.hAdd.arg_a4a5.fderiv_comp 
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (fwdDeriv K tag ι fun x => f x + g x)
    =
    fun x dx => 
      let ydy₁ := fwdDeriv K tag ι f x dx
      let ydy₂ := fwdDeriv K tag ι g x dx
      ydy₁ + ydy₂ := 
by 
  funext x dx
  unfold fwdDeriv; unfold broadcast
  ftrans only
  simp; rw[← map_add]; rfl


