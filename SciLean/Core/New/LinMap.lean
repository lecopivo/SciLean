-- import SciLean.Core.Data.Curry
import SciLean.Mathlib.Convenient.Basic
-- import SciLean.Core.New.IsSmooth
import SciLean.Core.New.TensorProduct

namespace SciLean

  def is_linear {X Y} [Vec X] [Vec Y] (f : X → Y) : Prop :=
    ∀ x y, f (x + y) = f x + f y
    ∧ 
    ∀ (s : ℝ) x, f (s*x) = s * (f x)

  structure LinMap (X Y : Type) [Vec X] [Vec Y] where
    val : X → Y 
    property : is_linear val ∧ Mathlib.Convenient.is_smooth val

  /-- `X --o Y` is the space of all linear maps between `X` and `Y`.

  The notation `X ⊸ Y` is prefered, but this fixes pure ASCII equivalent. -/
  infixr:25 " --o " => LinMap

  /-- `X ⊸ Y` is the space of all linear maps between `X` and `Y` -/
  infixr:25 " ⊸ " => LinMap


  variable {X Y : Type} [Vec X] [Vec Y]

  instance : Neg (X⊸Y) := ⟨λ f   => ⟨-f.1, sorry_proof⟩⟩
  instance : Add (X⊸Y) := ⟨λ f g => ⟨f.1 + g.1, sorry_proof⟩⟩
  instance : Sub (X⊸Y) := ⟨λ f g => ⟨f.1 - g.1, sorry_proof⟩⟩
  instance : Mul (X⊸ℝ) := ⟨λ f g => ⟨f.1 * g.1, sorry_proof⟩⟩
  instance : HMul ℝ (X⊸Y) (X⊸Y) := ⟨λ r f => ⟨r * f.1, sorry_proof⟩⟩
  instance : HMul (X⊸ℝ) (X⊸Y) (X⊸Y) := ⟨λ g f => ⟨λ x => g.1 x * f.1 x, sorry_proof⟩⟩
 
  instance : Zero (X ⊸ Y) := ⟨⟨0, sorry_proof⟩⟩
  instance [One Y] : One (X ⊸ Y) := ⟨⟨1, sorry_proof⟩⟩

  instance : AddSemigroup (X ⊸ Y) := AddSemigroup.mk sorry_proof
  instance : AddMonoid (X ⊸ Y)    := AddMonoid.mk sorry_proof sorry_proof nsmulRec sorry_proof sorry_proof
  instance : SubNegMonoid (X ⊸ Y) := SubNegMonoid.mk sorry_proof zsmulRec sorry_proof sorry_proof sorry_proof
  instance : AddGroup (X ⊸ Y)     := AddGroup.mk sorry_proof
  instance : AddCommGroup (X ⊸ Y) := AddCommGroup.mk sorry_proof

  instance : MulAction ℝ (X ⊸ Y) := MulAction.mk sorry_proof sorry_proof
  instance : DistribMulAction ℝ (X ⊸ Y) := DistribMulAction.mk sorry_proof sorry_proof
  instance : Module ℝ (X ⊸ Y) := Module.mk sorry_proof sorry_proof

  instance : Vec (X ⊸ Y) := Vec.mk

  instance : CoeFun (X⊸Y) (λ _ => X→Y) := ⟨λ f => f.1⟩

  --------------------------------------------------------------------

  @[ext] 
  theorem LinMap.ext {X Y} [Vec X] [Vec Y] (f g : X ⊸ Y) : (∀ x, f x = g x) → f = g := sorry

  variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
  
  namespace Linear

  def comp' : (Y ⊸ Z) → (X ⊸ Y) → (X ⊸ Z) := λ f g => ⟨λ x => f (g x), sorry_proof⟩

  noncomputable
  def curry' : (X ⊗ Y ⊸ Z) → (X ⊸ Y ⊸ Z) := λ f => ⟨λ x => ⟨λ y => f (x ⊗ y), sorry_proof⟩, sorry_proof⟩

  noncomputable 
  def uncurry' : (X ⊸ Y ⊸ Z) → (X ⊗ Y ⊸ Z) := λ f => ⟨λ xy => 
    let ⟨_,x,y⟩ := xy.repr
    ∑ i, f (x i) (y i), 
    sorry_proof⟩ -- we need to write and element of `X ⊗ Y` as ∑ i, c i * (x i ⊗ y i)

  def id : X ⊸ X := ⟨λ x => x, sorry_proof⟩
  def fst : X×Y ⊸ X := ⟨λ (x,y) => x, sorry_proof⟩
  def snd : X×Y ⊸ Y := ⟨λ (x,y) => y, sorry_proof⟩
  -- noncomputable
  -- def tprod : X×Y ⊸ X⊗Y := ⟨λ (x,y) => TensorProduct.tprod x y, sorry_proof⟩

  noncomputable
  def tpmap : (X⊸Y) ⊸ (X⊸Z) ⊸ (X⊸Y⊗Z) := ⟨λ f => ⟨λ g => ⟨λ x => (f x ⊗ g x), sorry_proof⟩, sorry_proof⟩, sorry_proof⟩
  noncomputable
  def tfmap : (X⊸Z) ⊸ (Y⊸W) ⊸ (X⊗Y⊸Z⊗W) := ⟨λ f => ⟨λ g => ⟨λ xy => 
    let ⟨_,x,y⟩ := xy.repr
    ∑ i, f (x i) ⊗ g (y i), sorry_proof⟩, sorry_proof⟩, sorry_proof⟩


  def pmap : (X⊸Y) × (X⊸Z) ⊸ (X⊸Y×Z) := ⟨λ (f,g) => ⟨λ x => (f x, g x), sorry_proof⟩, sorry_proof⟩
  def fmap : (X⊸Z) × (Y⊸W) ⊸ (X×Y⊸Z×W) := ⟨λ (f,g) =>⟨λ (x,y) => (f x, g y), sorry_proof⟩, sorry_proof⟩
  def fmap' : (X→Z) × (Y→W) ⊸ (X×Y→Z×W) := ⟨λ (f,g) => λ (x,y) => (f x, g y), sorry_proof⟩
  def pmap' : (X→Y) × (X→Z) ⊸ (X→Y×Z) := ⟨λ (f,g) => λ x => (f x, g x), sorry_proof⟩

  -- I don't think this is a valid map
  -- noncomputable
  -- def tfmap' : (X→Z) ⊸ (Y→W) ⊸ (X⊗Y→Z⊗W) := ⟨λ f => ⟨ λ g => λ xy => 
  --   let ⟨_,x,y⟩ := xy.repr
  --   ∑ i, f (x i) ⊗ g (y i), sorry_proof⟩, sorry_proof⟩

  noncomputable
  def tpmap' : (X→Y) ⊸ (X→Z) ⊸ (X→Y⊗Z) := ⟨λ f => ⟨λ g => λ x => f x ⊗ g x, sorry_proof⟩, sorry_proof⟩


  -- Does this one work?
  def comp'' : (Y ⊸ Z) ⊸ (X → Y) ⊸ (X → Z) := ⟨λ f => ⟨λ g => λ x => f (g x), sorry_proof⟩, sorry_proof⟩


  noncomputable
  def teval : ((X⊸Y)⊗X) ⊸ Y := uncurry' id
  noncomputable
  def tpair : X⊸Y⊸X⊗Y := curry' id

  
  def assocl : X×(Y×Z) ⊸ (X×Y)×Z := 
    let F : X×(Y×Z) ⊸ (X×Y)×Z := pmap ((pmap (fst, (comp' fst snd))), (comp' snd snd))
    ⟨λ (x,(y,z)) => ((x,y),z), 
     by 
       have h : (λ (x,(y,z)) => ((x,y),z)) = F.1 := by simp[pmap, comp', fst, snd]
       rw[h]
       apply F.2⟩

  def assocr : (X×Y)×Z ⊸ X×(Y×Z) := 
    let F : (X×Y)×Z ⊸ X×(Y×Z) := pmap ((comp' fst fst), (pmap ((comp' snd fst), snd)))
    ⟨λ ((x,y),z) => (x,(y,z)),
     by 
       have h : (λ ((x,y),z) => (x,(y,z))) = F.1 := by simp[pmap, comp', fst, snd]
       rw[h]
       apply F.2⟩

  @[simp]
  theorem assocl_eval (xyz : X×(Y×Z)) : assocl xyz = ((xyz.1,xyz.2.1),xyz.2.2) := rfl

  @[simp]
  theorem assocr_eval (xyz : (X×Y)×Z) : assocr xyz = (xyz.1.1,(xyz.1.2,xyz.2)) := rfl

  noncomputable
  def tassocl : X⊗(Y⊗Z) ⊸ (X⊗Y)⊗Z := ⟨λ xyz => 
    let ⟨_,x,yz⟩ := xyz.repr
    let y := λ i => (yz i).repr.snd.fst
    let z := λ i => (yz i).repr.snd.snd
    ∑ i j, (x i ⊗ y i j) ⊗ z i j,
    sorry_proof⟩

  noncomputable
  def tassocr : (X⊗Y)⊗Z ⊸ X⊗(Y⊗Z) := ⟨λ xyz => 
    let ⟨_,xy,z⟩ := xyz.repr
    let x := λ i => (xy i).repr.snd.fst
    let y := λ i => (xy i).repr.snd.snd
    ∑ i j, x i j ⊗ (y i j ⊗ z i),
    sorry_proof⟩

  def swap : (X×Y) ⊸ (Y×X) := pmap (snd, fst)

  @[simp]
  theorem swap_eval (xy : (X×Y)) : swap xy = (xy.2, xy.1) := rfl

  noncomputable
  def tswap : (X⊗Y) ⊸ (Y⊗X) := ⟨λ xy => 
    let ⟨_,x,y⟩ := xy.repr
    ∑ i, y i ⊗ x i,
    sorry_proof⟩

  def rot132 : (X×Y)×Z ⊸ (X×Z)×Y := comp' assocl (comp' (fmap (id, swap)) assocr)

  @[simp]
  theorem rot132_eval (xyz : (X×Y)×Z) : rot132 xyz = ((xyz.1.1, xyz.2), xyz.1.2) := rfl

  noncomputable
  def trot132 : (X⊗Y)⊗Z ⊸ (X⊗Z)⊗Y := comp' tassocl (comp' (tfmap id tswap) tassocr)

  @[simp]
  theorem trot132_eval (x : X) (y : Y) (z : Z) : trot132 ((x⊗y)⊗z) = (x⊗z)⊗y := sorry_proof

  -- TODO: This function is perfectly computable, make it so
  -- only the proof of linearity goes via noncomputable tensor product
  noncomputable
  def comp : (Y ⊸ Z) ⊸ (X ⊸ Y) ⊸ (X ⊸ Z) := 
    let F₁ : (Y⊸Z)⊗((X⊸Y)⊗X) ⊸ Z := comp' teval (tfmap id teval)
    curry' (curry' (comp' F₁ tassocr))


  @[simp]
  theorem comp_eval (f : Y⊸Z) (g : X ⊸ Y) (x : X) : comp f g x = f (g x) := sorry_proof

  -- def const : X⊸Y⊸X := curry' fst

  -- @[simp]
  -- theorem const_eval (f : Y⊸Z) (g : X ⊸ Y) (x : X) : comp f g x = f (g x) := rfl

  noncomputable
  def uncurry : (X ⊸ Y ⊸ Z) ⊸ (X⊗Y ⊸ Z) := 
    let F : ((X⊸Y⊸Z)⊗X)⊗Y ⊸ Z := comp teval (tfmap teval id)

    let G₁ : (X⊗Y ⊸ (X⊸Y⊸Z)⊗(X⊗Y)) ⊸ (X⊗Y ⊸ Z) := comp (comp' F tassocl)
    let G₂ : (X⊸Y⊸Z) ⊸ (X⊗Y ⊸ (X⊸Y⊸Z)⊗(X⊗Y)) := tpair
    comp' G₁ G₂

  -- @[simp]
  -- theorem Smooth.uncurry_eval (f : X ⊸ Y ⊸ Z) (xy : X×Y) : Smooth.uncurry f xy = f xy.1 xy.2 := by rfl
  
  noncomputable
  def curry : (X ⊗ Y ⊸ Z) ⊸ (X ⊸ Y ⊸ Z) := 

    let G : ((X⊗Y⊸Z)⊗Y)⊗X ⊸ Z := comp (comp (uncurry' id) (tfmap id tswap)) tassocr

    let H : (Y ⊸ (X⊗Y⊸Z)⊗Y)⊗X ⊸ (Y ⊸ ((X⊗Y⊸Z)⊗Y)⊗X) := curry' (comp (tfmap teval id) trot132)

    let F₁ : (X⊗Y⊸Z) ⊸ (Y ⊸ (X⊗Y⊸Z)⊗Y) := tpair
    let F₂ : (Y ⊸ (X⊗Y⊸Z)⊗Y) ⊸ (X ⊸ (Y ⊸ (X⊗Y⊸Z)⊗Y)⊗X) := tpair
    let F₃ : (X ⊸ (Y ⊸ (X⊗Y⊸Z)⊗Y)⊗X) ⊸ (X ⊸ (Y ⊸ ((X⊗Y⊸Z)⊗Y)⊗X)) := comp H

    comp (comp (comp G)) (comp F₃ (comp F₂ F₁))

  -- @[simp]
  -- theorem Smooth.curry_eval (f : X×Y ⊸ Z) (x : X) (y : Y) : Smooth.curry f x y = f (x,y) := by rfl

  -- TODO: make it computable
  noncomputable 
  def prod : (X → Y ⊸ Z) ⊸ (X→Y) ⊸ (X→Z) := 
    let F : (X → Y ⊸ Z) ⊸ (X→Y) ⊸ (X → Y ⊸ Z)⊗(X→Y) := tpair
    let G₁ : (X → Y ⊸ Z)⊗(X→Y) ⊸ (X → (Y⊸Z)⊗Y) := uncurry tpmap'
    let G₂ : (X → (Y⊸Z)⊗Y) ⊸ (X→Z) := comp'' teval
    
    comp (comp (comp G₂ G₁)) F

  @[simp]
  theorem prod_eval (f : X → Y ⊸ Z) : prod f (λ _ => y) x = f x y := sorry_proof

  -- def scomb : (X⊸Y⊸Z) ⊸ (X⊸Y) ⊸ X ⊸ Z := 
  --   let F₁ : (X⊸Y⊸Z)⊗(X⊸Y)⊗X ⊸ (X⊗Y⊸Z)⊗(X⊗Y) := tfmap uncurry (tpmap snd teval)
  --   comp (curry) (curry (comp eval F₁))


  -- variable {ι κ : Type} {E F G : ι → Type} {E' : κ → Type} [∀ i, Vec (E i)] [∀ i, Vec (F i)] [∀ i, Vec (G i)] [∀ j, Vec (E' j)]
  -- instance  [∀ i, Vec (F i)] : Vec ((i : ι) → (F i)) := sorry

  -- def Smooth.pmapDep : ((i : ι)→(E i)) ⊸ ((i : ι)→(F i)) ⊸ ((i : ι)→(E i)×(F i)) := ⟨λ f => ⟨λ g => λ x => (f x, g x), sorry⟩, sorry⟩
  -- def Smooth.fmapDep : ((i : ι)→(E i)) ⊸ ((j : κ)→(E' j)) ⊸ ((ij : (ι×κ))→(E ij.1)×(E' ij.2)) := ⟨λ f => ⟨λ g => λ (i,j) => (f i, g j), sorry⟩, sorry⟩
  -- def Smooth.prodDep : ((i : ι) → E i ⊸ F i) ⊸ ((i : ι) → E i) ⊸ ((i : ι) → F i) := sorry 


  end Linear

