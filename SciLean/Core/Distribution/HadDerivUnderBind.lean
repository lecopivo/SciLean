import SciLean.Core.Distribution.Basic
import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Distribution.RestrictToLevelSet

import SciLean.Tactic.GTrans

open MeasureTheory

namespace SciLean

variable
  {R} [RealScalar R]
  {W} [Vec R W] [Module ℝ W]
  {X} [Vec R X] -- [TopologicalSpace X] [space : TCOr (Vec R X) (DiscreteTopology X)]
  {Y} [Vec R Y] [Module ℝ Y]
  {Z} [Vec R Z]
  {U} [Vec R U] [Module ℝ U]
  {U₁} [Vec R U₁] [Module ℝ U₁]
  {U₂} [Vec R U₂] [Module ℝ U₂]
  {V} [Vec R V] [Module ℝ V]
  {S} [Vec R S]

set_default_scalar R


variable (R)

@[gtrans]
def HasDerivUnderBind
    (f : W → X → 𝒟' Y) (u : 𝒟' X) (w : W)
    (f' : outParam <| W → X → 𝒟' Y) (s : outParam <| W → 𝒟' Y) : Prop :=
  ∀ dw, parDistribDeriv (fun w' => u.bind (f w') (fun a ⊸ fun b ⊸ a * b)) w dw
        =
        u.bind (f' w) (fun a ⊸ fun b ⊸ a * b)
        +
        s dw


@[gtrans]
def HasDerivUnderBind'
    (f : W → X → 𝒟'(Y,V)) (u : 𝒟'(X,U)) (L : U ⊸ V ⊸ W) (w : W)
    (f' : outParam <| W → X → 𝒟'(Y,V)) (s : outParam <| W → 𝒟'(Y,W)) : Prop :=
  ∀ dw, parDistribDeriv (fun w' => u.bind (f w') L) w dw
        =
        u.bind (f' w) L
        +
        s dw


variable {R}


@[fun_trans]
theorem bind.arg_f.cderiv_rule
    (f : W → X → 𝒟' Y) (u : 𝒟' X) (w : W)
    (f' : W → X → 𝒟' Y) (sf : W → 𝒟' Y)
    (hf : HasDerivUnderBind R f u w f' sf) :
    (∂ (w':=w), u.bind (f w') (fun a ⊸ fun b ⊸ a * b))
    =
    fun dw =>
      let di := u.bind (f' dw) (fun a ⊸ fun b ⊸ a * b)
      let sf' := sf dw
      di + sf' := sorry_proof

@[gtrans]
theorem hasDerivUnderBind_of_differentiable_over_measure [MeasurableSpace X]
    (f : W → X → 𝒟' Y) (u : 𝒟' X) (w : W)
    (hu : u.IsMeasure)
    (hf : ∀ x, CDifferentiable R (fun w' => f w' x))
    /- u.measure-integrability of `f` -/ :
    HasDerivUnderBind R f u w
      (fun dw x => ∂ (w':=w;dw), f w' x)
      0 := sorry_proof


@[gtrans]
theorem HAdd.hAdd.arg_a0a1.HasDerivUnderBind_rule
  (f g : W → X → 𝒟' Y) (u : 𝒟' X) (w : W)
  (f' g' : W → X → 𝒟' Y) (sf sg : W → 𝒟' Y)
  (hf : HasDerivUnderBind R f u w f' sf)
  (hg : HasDerivUnderBind R g u w g' sg) :
  HasDerivUnderBind R
  (fun w x => f w x + g w x) u w
  (fun dw x =>
   let df := f' dw x
   let dg := g' dw x
   df + dg)
  (fun dw =>
   let sf' := sf dw
   let sg' := sg dw
   sf' + sg') := sorry_proof

@[gtrans]
theorem Sub.hSub.arg_a0a1.HasDerivUnderBind_rule
  (f g : W → X → 𝒟' Y) (u : 𝒟' X) (w : W)
  (f' g' : W → X → 𝒟' Y) (sf sg : W → 𝒟' Y)
  (hf : HasDerivUnderBind R f u w f' sf)
  (hg : HasDerivUnderBind R g u w g' sg) :
  HasDerivUnderBind R
  (fun w x => f w x - g w x) u w
  (fun dw x =>
   let df := f' dw x
   let dg := g' dw x
   df - dg)
  (fun dw =>
   let sf' := sf dw
   let sg' := sg dw
   sf' - sg') := sorry_proof


@[gtrans]
theorem Neg.neg.arg_a0.HasDerivUnderBind_rule
  (f : W → X → 𝒟' Y) (u : 𝒟' X) (w : W)
  (f' : W → X → 𝒟' Y) (sf : W → 𝒟' Y)
  (hf : HasDerivUnderBind R f u w f' sf) :
  HasDerivUnderBind R
    (fun w x => -f w x) u w
    (fun dw x =>
       let df := f' dw x
       (-df))
    (fun dw =>
       let sf' := sf dw
       (-sf')) := sorry_proof



@[gtrans]
theorem HSMul.hSMul.arg_a1.HasDerivUnderBind_rule
  (c : R) (f : W → X → 𝒟' Y) (u : 𝒟' X) (w : W)
  (f' : W → X → 𝒟' Y) (sf : W → 𝒟' Y)
  (hf : HasDerivUnderBind R f u w f' sf) :
  HasDerivUnderBind R
    (fun w x => c • f w x) u w
    (fun dw x =>
       let df := f' dw x
       c • df)
    (fun dw =>
       let sf' := sf dw
       c • sf') := sorry_proof


@[gtrans]
theorem bind.arg_f.HadDerivUnderBind_rule
  (w : W) (f : W → X → Y → 𝒟' Z) (u : 𝒟' X) (v : 𝒟' Y)
  (f' : W → X×Y → 𝒟' Z) (sf : W → 𝒟' Z)
  (hf : HasDerivUnderBind R (fun w (xy : X×Y) => f w xy.1 xy.2) (u.prod Prod.mk (fun _ => v) sorry) w f' sf) :
  HasDerivUnderBind R
    (fun w x => v.bind (f w x) sorry) u w
    (fun dw x => v.bind (fun y => f' dw (x,y)) sorry) sf := sorry_proof

variable
  {W₂} [Vec R W₂] [Module ℝ W₂]

#check TensorProduct R U V
#check TensorProduct.tmul

instance {X} {Y} [AddCommMonoid X] [AddCommMonoid Y] [Module R X] [Module R Y] [UniformSpace X] [UniformSpace Y] :
    UniformSpace (TensorProduct R X Y) where
  IsOpen := sorry
  isOpen_univ := sorry_proof
  isOpen_inter := sorry_proof
  isOpen_sUnion := sorry_proof
  uniformity := sorry
  symm := sorry_proof
  comp := sorry_proof
  nhds_eq_comap_uniformity := sorry_proof

noncomputable
instance {X} {Y} [Vec R X] [Vec R Y] : Vec R (TensorProduct R X Y) where
  uniformContinuous_sub := sorry_proof
  continuous_smul := sorry_proof
  scalar_wise_smooth := sorry_proof

def tmul' : U ⊸ V ⊸ TensorProduct R U V := sorry

def tuncurry (f : U ⊸ V ⊸ W) : TensorProduct R U V ⊸ W := sorry

variable (K₂ : U₂ ⊸ V ⊸ W₂) (L₂ : U₁ ⊸ W₂ ⊸ W) (f : U ⊸ V)

#check fun f : U⊸V => fun u => f u

example (f : U ⊸ V)
  (K₂ : U₂ ⊸ V ⊸ W₂) (L₂ : U₁ ⊸ W₂ ⊸ W) :
  IsSmoothLinearMap R (X:=U) (Y:=V) (fun u => f u) := by fun_prop

example (f : U ⊸ V)
  (K₂ : U₂ ⊸ V ⊸ W₂) (L₂ : U₁ ⊸ W₂ ⊸ W) :
  IsSmoothLinearMap R (fun v => fun u₁ ⊸ fun u ⊸ L₂ u₁ (K₂ u v)) := by fun_prop


@[gtrans]
theorem bind.arg_f.HadDerivUnderBind'_rule
  (w : W) (f : W → X → Y → 𝒟'(Z,V)) (u : 𝒟'(X,U₁)) (v : 𝒟'(Y,U₂)) (L : U ⊸ V ⊸ W) (K : U₁ ⊸ U₂ ⊸ U) (K₂ : U₂ ⊸ V ⊸ W₂) (L₂ : U₁ ⊸ W₂ ⊸ W)
  (f' : W → X×Y → 𝒟'(Z,V)) (sf : W → 𝒟'(Z,W))
  (hf : HasDerivUnderBind' R (fun w (xy : X×Y) => f w xy.1 xy.2) (u.prod Prod.mk (fun _ => v) tmul') (tuncurry (fun u₁ ⊸ fun u₂ ⊸ fun v ⊸ L₂ u₁ (K₂ u₂ v))) w f' sf) :
  HasDerivUnderBind' R
    (fun w x => v.bind (f w x) K₂) u L₂ w
    (fun dw x => v.bind (fun y => f' dw (x,y)) K₂) sf := sorry_proof



@[gtrans]
theorem ite.arg_cte.HasDerivUnderBind_rule {X} [SemiHilbert R X] [MeasureSpace X]
  (t e : W → X → 𝒟' Y) (u : 𝒟' X) (w : W)
  (c : W → X → Prop) [∀ w x, Decidable (c w x)]
  (t' e' : W → X → 𝒟' Y) (st se : W → 𝒟' Y)
  (hu : u.IsFunction) -- works only for distributions with density
  (hf : HasDerivUnderBind R t (u.restrict {x | c w x}) w t' st)
  (hg : HasDerivUnderBind R e (u.restrict {x | c w x}ᶜ) w e' se) :
  HasDerivUnderBind R
    (fun w x => if c w x then t w x else e w x) u w
    (fun dw x => if c w x then t' dw x else e' dw x)
    (fun dw =>
       let ds :=
         (u.restrictToFrontier R (fun w => {x | c w x}) w dw)
         |>.bind (fun x => t w x - e w x) (fun x ⊸ fun y ⊸ x*y)
       let st' := st dw
       let se' := se dw
       st' + se' + ds) := sorry_proof


@[gtrans]
theorem ite.arg_cte.HasDerivUnderBind'_rule {X} [SemiHilbert R X] [MeasureSpace X]
  (t e : W → X → 𝒟'(Y,V)) (u : 𝒟'(X,U)) (L : U ⊸ V ⊸ W) (w : W)
  (c : W → X → Prop) [∀ w x, Decidable (c w x)]
  (t' e' : W → X → 𝒟'(Y,V)) (st se : W → 𝒟'(Y,W))
  (hu : u.IsFunction) -- works only for distributions with density
  (hf : HasDerivUnderBind' R t (u.restrict {x | c w x}) L w t' st)
  (hg : HasDerivUnderBind' R e (u.restrict {x | c w x}ᶜ) L w e' se) :
  HasDerivUnderBind' R
    (fun w x => if c w x then t w x else e w x) u L w
    (fun dw x => if c w x then t' dw x else e' dw x)
    (fun dw =>
       let ds :=
         (u.restrictToFrontier R (fun w => {x | c w x}) w dw)
         |>.bind (fun x => t w x - e w x) L
       let st' := st dw
       let se' := se dw
       st' + se' + ds) := sorry_proof
