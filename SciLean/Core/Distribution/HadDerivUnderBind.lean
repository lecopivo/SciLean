import SciLean.Core.Distribution.Basic
import SciLean.Core.Distribution.ParametricDistribDeriv


namespace SciLean

variable
  {R} [RealScalar R]
  {W} [Vec R W] [Module ℝ W]
  {X} [Vec R X] -- [TopologicalSpace X] [space : TCOr (Vec R X) (DiscreteTopology X)]
  {Y} [Vec R Y] [Module ℝ Y]
  {Z} [Vec R Z]
  {U} [Vec R U]
  {V} [Vec R V]

set_default_scalar R


variable (R)

def HasDerivUnderBind
    (f : W → X → 𝒟' Y) (u : 𝒟' X) (w : W)
    (f' : outParam <| W → X → 𝒟' Y) (s : outParam <| W → 𝒟' Y) : Prop :=
  ∀ dw, parDistribDeriv (fun w' => u.bind (f w') (fun a ⊸ fun b ⊸ a * b)) w dw
        =
        u.bind (f' w) (fun a ⊸ fun b ⊸ a * b)
        +
        s dw

variable {R}


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


theorem hasDerivUnderBind_of_differentiable_over_measure [MeasurableSpace X]
    (f : W → X → 𝒟' Y) (u : 𝒟' X) (w : W)
    (hu : u.IsMeasure)
    (hf : ∀ x, CDifferentiable R (fun w' => f w' x))
    /- u.measure-integrability of `f` -/ :
    ∂ (w':=w), u.bind (f w) (fun a ⊸ fun b ⊸ a*b)
    =
    fun dw =>
      let df := ∂ (w':=w;dw), f w'
      u.bind df (fun a ⊸ fun b ⊸ a*b) := sorry_proof


theorem hasDerivUnderBind_of_differentiable_over_dirac [MeasurableSpace X]
    (f : W → X → 𝒟' Y) (x : X) (w : W)
    (hf : CDifferentiable R (fun (w,x) => f w x)) :
    ∂ (w':=w), (dirac x).bind (f w) (fun a ⊸ fun b ⊸ a*b)
    =
    fun dw =>
      let dy := ∂ (w':=w;dw), f w' x
      dy := sorry_proof


theorem ite.arg_cte.HasDerivUnderBind_rule
  (t e : W → X → 𝒟' Y) (u : 𝒟' X) (w : W)
  (c : W → X → Prop) [∀ w x, Decidable (c w x)]
  (t' e' : W → X → 𝒟' Y) (st se : W → 𝒟' Y)
  (hf : HasDerivUnderBind R t (u.restrict {x | c w x}) w t' st)
  (hg : HasDerivUnderBind R e (u.restrict {x | c w x}ᶜ) w e' se) :
  HasDerivUnderBind R
    (fun w x => if c w x then t w x else e w x) u w
    (fun dw x => if c w x then t' dw x else e' dw x)
    (fun dw =>
       let ds := sorry
       let st' := st dw
       let se' := se dw
       st' + se' + ds) := sorry_proof


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
