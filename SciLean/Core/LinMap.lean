-- import SciLean.Core.Data.Curry
import SciLean.Mathlib.Convenient.Basic
-- import SciLean.Core.New.IsSmooth
import SciLean.Core.TensorProduct
import SciLean.Core.FinVec
import SciLean.Core.SmoothMap

namespace SciLean


@[fun_prop_def]
structure IsLin {X Y : Type _} [Vec X] [Vec Y] (f : X → Y) : Prop where
 isLin : TensorProduct.is_linear f 
 isSmooth : IsSmooth f

structure LinMap (X Y : Type _) [Vec X] [Vec Y] where
  toFun : X → Y 
  isLin_toFun : IsLin toFun := by infer_instance

/-- `X --o Y` is the space of all linear maps between `X` and `Y`.

The notation `X ⊸ Y` is prefered, but this fixes pure ASCII equivalent. -/
infixr:25 " --o " => LinMap

/-- `X ⊸ Y` is the space of all linear maps between `X` and `Y` -/
infixr:25 " ⊸ " => LinMap

-- Lambda notation
open Lean.TSyntax.Compat in
macro "λ"   xs:Lean.explicitBinders " ⊸ " b:term : term =>
  Lean.expandExplicitBinders `SciLean.LinMap.mk xs b
open Lean.TSyntax.Compat in
macro "fun"   xs:Lean.explicitBinders " ⊸ " b:term : term =>
  Lean.expandExplicitBinders `SciLean.LinMap.mk xs b

class LinMapClass (F : Type _) (X Y : outParam <| Type _) [Vec X] [Vec Y]
  extends FunLike F X fun _ => Y where
  map_isLin (f : F) : IsLin f

export LinMapClass (map_isLin)

attribute [fun_prop] map_isLin

section LinMapClass

  -- The following is heavily inspired by ContinuousMap

  variable {F X Y : Type _} [Vec X] [Vec Y] [LinMapClass F X Y]

  instance : CoeTC F (X ⊸ Y) :=
    ⟨fun f =>
      { toFun := f
        isLin_toFun := map_isLin f }⟩

end LinMapClass

namespace LinMap

  variable {X Y Z W : Type _} [Vec X] [Vec Y] [Vec Z] [Vec W]

  instance : LinMapClass (X⊸Y) X Y where
    map_isLin f := f.isLin_toFun
    coe f := f.toFun
    coe_injective' := sorry_proof
    
  @[simp]
  theorem toFun_eq_coe {f : X ⊸ Y} : f.toFun = (f : X → Y) :=
    rfl

  def Simps.apply (f : X ⊸ Y) : X → Y := f

  initialize_simps_projections LinMap (toFun → apply)

  @[simp]
  protected theorem coe_coe {F : Type} [LinMapClass F X Y] (f : F) : ⇑(f : X ⊸ Y) = f :=
    rfl

  @[ext]
  theorem ext {f g : X ⊸ Y} (h : ∀ x, f x = g x) : f = g :=
    FunLike.ext _ _ h

  @[fun_prop]
  theorem isLin_set_coe (s : Set (X⊸Y)) (f : s) : IsLin (f : X → Y) :=
    map_isLin f.1

  @[simp]
  theorem coe_mk (f : X → Y) (h : IsLin f) : ⇑(⟨f, h⟩ : X ⊸ Y) = f :=
    rfl

  @[simp]
  theorem eta (f : X ⊸ Y)
      : (λ (x : X) ⊸ f x) = f := by rfl; done

  protected def id : X ⊸ X :=
    LinMap.mk (λ x => x) sorry

  @[simp]
  theorem coe_id : ⇑(LinMap.id : X ⊸ X) = _root_.id := 
    rfl

  @[simp]
  theorem id_apply (x : X) : LinMap.id x = x :=
    rfl

  ------------------------------------------------------------------------------
  -- X ⊸ Y is vector space 
  ------------------------------------------------------------------------------

  theorem show_is_lin_via {X Y} [Vec X] [Vec Y] {f : X → Y} (g : X ⊸ Y) : (f = g) → IsLin f :=
  by
    intro p
    have q : f = g := by apply p
    rw[q]; infer_instance

  def comp' : (Y⊸Z) → (X⊸Y) → (X⊸Z) := λ f g =>
    LinMap.mk (λ x => f (g x)) sorry

  def prodMap' : (X⊸Y) → (X⊸Z) → (X ⊸ Y×Z) := λ f g =>
    LinMap.mk (λ x => (f x, g x)) sorry

  def zeroFun : Y⊸X :=
    LinMap.mk (λ y => (0 : X)) sorry

  def swap : X⊗Y → Y⊗X := (λ xy => xy.map' (λ (x : X) (y : Y) => y⊗x) sorry)

  @[simp] theorem comp'_eval (f : Y ⊸ Z) (g : X⊸Y) (x : X) : comp' f g x = f (g x) := by simp[comp']
  @[simp] theorem prodMap'_eval (f : X ⊸ Y) (g : X⊸Z) (x : X) : prodMap' f g x = (f x, g x) := by simp[prodMap']
  @[simp] theorem zeroFun_eval (y : Y) : zeroFun y = (0 : X) := by simp[zeroFun]


  def neg : X ⊸ X := LinMap.mk (λ x => -x) sorry
  def add' : X×X ⊸ X := LinMap.mk (λ (x,y) => x+y) sorry
  def sub' : X×X ⊸ X := LinMap.mk (λ (x,y) => x-y) sorry
  def mul' : ℝ×ℝ ⊸ ℝ := LinMap.mk (λ (x,y) => x*y) sorry

  -- def tassocl : 
  -- def tassocr : 
  def unit' : ℝ → X ⊸ ℝ⊗X := λ r => LinMap.mk (λ x => r⊗x) sorry
  def counit : ℝ⊗X ⊸ X := LinMap.mk ((λ rx => rx.map' (λ r x => r • x) sorry)) sorry

  @[simp] theorem unit'_eval (r : ℝ) (x : X) : unit' r x = r⊗x := by simp[unit']
  @[simp] theorem counit_eval (r : ℝ) (x : X) : counit (r⊗x) = r•x := by simp[counit]

  instance : Neg (X⊸Y) := ⟨λ f => LinMap.mk (λ x => -f x)
    (show_is_lin_via (comp' neg f) (by funext; simp[neg]))⟩

  instance : Add (X⊸Y) := ⟨λ f g => LinMap.mk (λ x => f x + g x)
    (show_is_lin_via (comp' add' (prodMap' f g)) (by funext; simp[add']))⟩

  instance : Sub (X⊸Y) := ⟨λ f g => LinMap.mk (λ x => f x - g x)
    (show_is_lin_via (comp' sub' (prodMap' f g)) (by funext; simp[sub']))⟩

  instance : Mul (X⊸ℝ) := ⟨λ f g => LinMap.mk (λ x => f x * g x)
    (show_is_lin_via (comp' mul' (prodMap' f g)) (by funext; simp[mul']))⟩

  instance : SMul ℝ (X⊸Y) := ⟨λ r f => LinMap.mk (λ x => r • f x)
    (show_is_lin_via (comp' counit (comp' (unit' r) f)) (by funext; simp))⟩

  instance : Zero (X ⊸ Y) := ⟨zeroFun⟩

  -- !!!THIS USES SORRY!!!
  instance : Vec (X ⊸ Y) := Vec.mkSorryProofs


  def _root_.SciLean.TensorProduct.map (f : X ⊸ Y ⊸ Z) (xy : X⊗Y) : Z := xy.map' (λ x y => f x y) sorry_proof

  section FinVec 

    variable {X Y : Type _} {ι κ} {_ : Enumtype ι} {_ : Enumtype κ}

  -- @[infer_tc_goals_rl]
    instance [FinVec X ι] [Hilbert Y] : Inner (X ⊸ Y) where
      -- This should be the correct version of the inner product
      -- It looks assymetrical but it is a consequence of `inner_proj_dualproj`
      --   ⟪x, y⟫ = ∑ i, 𝕡 i x * 𝕡' i y
      -- which also appears assymetrical
      inner f g := ∑ i, ⟪f (𝕖 i), g (𝕖' i)⟫

    -- @[infer_tc_goals_rl]
    instance [FinVec X ι] [Hilbert Y] : TestFunctions (X ⊸ Y) where
      TestFun _ := True

    -- @[infer_tc_goals_rl]
    instance [FinVec X ι] [Hilbert Y] : SemiHilbert (X ⊸ Y) := SemiHilbert.mkSorryProofs

    -- @[infer_tc_goals_rl]
    instance [FinVec X ι] [Hilbert Y] : Hilbert (X ⊸ Y) := Hilbert.mkSorryProofs

    -- @[infer_tc_goals_rl]
    instance [FinVec X ι] [FinVec Y κ] : Basis (X ⊸ Y) (ι×κ) ℝ where
      basis := λ (i,j) => LinMap.mk (λ x => 𝕡 i x • 𝕖[Y] j) sorry_proof
      proj := λ (i,j) f => 𝕡 j (f (𝕖 i))

    -- @[infer_tc_goals_rl]
    instance [FinVec X ι] [FinVec Y κ] : DualBasis (X ⊸ Y) (ι×κ) ℝ where
      dualBasis := λ (i,j) => LinMap.mk (λ x => 𝕡' i x • 𝕖'[Y] j) sorry_proof
      dualProj := λ (i,j) f => 𝕡' j (f (𝕖' i))

    open BasisDuality in
    -- @[infer_tc_goals_rl]
    instance [FinVec X ι] [FinVec Y κ] : BasisDuality (X ⊸ Y) where
      toDual   := λ f => LinMap.mk (λ x => toDual (f (fromDual x))) sorry_proof
      fromDual := λ f => LinMap.mk (λ x => fromDual (f (toDual x))) sorry_proof

    -- @[infer_tc_goals_rl]
    instance [FinVec X ι] [FinVec Y κ] : FinVec (X ⊸ Y) (ι×κ) where     
      is_basis := sorry_proof
      duality := by 
        intro (i,j) (i',j'); simp[Basis.basis, DualBasis.dualBasis, Inner.inner];
        -- This should be:
        --  ∑ i_i, ⟪[[i=i_]] * 𝕖 j, [[i'=i_1]] 𝕖' j'⟫
        --  [[i=i']] * ⟪𝕖 j, 𝕖' j'⟫
        --  [[i=i']] * [[j=j']]
        sorry_proof
      to_dual := by
        simp [BasisDuality.toDual, Basis.proj, DualBasis.dualBasis]
        intro f; ext x; 
        simp[FinVec.to_dual,FinVec.from_dual]
        -- Now the goal is:
        --   ∑ j, 𝕡 j (f (∑ i, 𝕡' i x * 𝕖 i)) * 𝕖' j
        --   =
        --   ∑ (i,j), 𝕡 j (f (𝕖 i)) * 𝕡' i x * 𝕖' j
        sorry_proof
      from_dual := by
        simp [BasisDuality.fromDual, DualBasis.dualProj, Basis.basis]
        intro f; ext x; 
        simp[FinVec.to_dual,FinVec.from_dual]
        -- Now the goal is:
        --   ∑ j, 𝕡' j (f (∑ i, 𝕡 i x * 𝕖' i)) * 𝕖 j
        --   =
        --   ∑ (i,j), 𝕡' j (f (𝕖' i)) * 𝕡' i x * 𝕖 j
        sorry_proof

  end FinVec 


  ------------------------------------------------------------------------------
  -- Basic combinators like const, comp, curry, uncurry, prodMk, prodMap, pi
  ------------------------------------------------------------------------------


  def curry' (f : X ⊗ Y ⊸ Z) : (X ⊸ Y ⊸ Z) := 
    LinMap.mk (λ x => 
      LinMap.mk (λ y => f (x ⊗ y)) 
      sorry_proof) 
    sorry_proof

  def uncurry' (f : X ⊸ Y ⊸ Z) : (X ⊗ Y ⊸ Z) := 
    LinMap.mk (λ xy => xy.map' (λ x y => f x y) sorry_proof) sorry_proof

  def fst : X×Y ⊸ X := LinMap.mk (λ (x,_) => x) sorry_proof
  def snd : X×Y ⊸ Y := LinMap.mk (λ (_,y) => y) sorry_proof

  @[simp] theorem curry'_eval (f : X⊗Y ⊸ Z) (x : X) (y : Y) : curry' f x y = f (x⊗y) := by simp[curry']
  @[simp] theorem uncurry'_eval (f : X ⊸ Y ⊸ Z) (xy : X⊗Y) : uncurry' f xy = xy.map f := by simp[uncurry',TensorProduct.map]
  @[simp] theorem id_eval (x : X) : id x = x := by simp[id]
  @[simp] theorem fst_eval (xy : X×Y) : fst xy = xy.1 := by simp[fst]
  @[simp] theorem snd_eval (xy : X×Y) : snd xy = xy.2 := by simp[snd]

  def tprod : X ⊸ Y ⊸ X⊗Y := 
    LinMap.mk (λ x => 
      LinMap.mk (λ y => x⊗y)
      (show_is_lin_via (curry' LinMap.id x) (by ext y; simp)))
    (show_is_lin_via (curry' LinMap.id) (by ext x y; simp))

  -- noncomputable
  -- def tpmap : (X⊸Y) ⊸ (X⊸Z) ⊸ (X⊸Y⊗Z) := ⟨λ f => ⟨λ g => ⟨λ x => (f x ⊗ g x), sorry_proof⟩, sorry_proof⟩, sorry_proof⟩
  -- noncomputable
  -- def tfmap : (X⊸Z) ⊸ (Y⊸W) ⊸ (X⊗Y⊸Z⊗W) := ⟨λ f => ⟨λ g => ⟨λ xy => 
  --   let ⟨_,x,y⟩ := xy.repr
  --   ∑ i, f (x i) ⊗ g (y i), sorry_proof⟩, sorry_proof⟩, sorry_proof⟩


  -- def pmap : (X⊸Y) × (X⊸Z) ⊸ (X⊸Y×Z) := ⟨λ (f,g) => ⟨λ x => (f x, g x), sorry_proof⟩, sorry_proof⟩
  -- def fmap : (X⊸Z) × (Y⊸W) ⊸ (X×Y⊸Z×W) := ⟨λ (f,g) =>⟨λ (x,y) => (f x, g y), sorry_proof⟩, sorry_proof⟩
  -- def fmap' : (X→Z) × (Y→W) ⊸ (X×Y→Z×W) := ⟨λ (f,g) => λ (x,y) => (f x, g y), sorry_proof⟩
  -- def pmap' : (X→Y) × (X→Z) ⊸ (X→Y×Z) := ⟨λ (f,g) => λ x => (f x, g x), sorry_proof⟩

  -- -- I don't think this is a valid map
  -- -- noncomputable
  -- -- def tfmap' : (X→Z) ⊸ (Y→W) ⊸ (X⊗Y→Z⊗W) := ⟨λ f => ⟨ λ g => λ xy => 
  -- --   let ⟨_,x,y⟩ := xy.repr
  -- --   ∑ i, f (x i) ⊗ g (y i), sorry_proof⟩, sorry_proof⟩

  -- noncomputable
  -- def tpmap' : (X→Y) ⊸ (X→Z) ⊸ (X→Y⊗Z) := ⟨λ f => ⟨λ g => λ x => f x ⊗ g x, sorry_proof⟩, sorry_proof⟩


  -- -- Does this one work?
  -- def comp'' : (Y ⊸ Z) ⊸ (X → Y) ⊸ (X → Z) := ⟨λ f => ⟨λ g => λ x => f (g x), sorry_proof⟩, sorry_proof⟩


  -- noncomputable
  -- def teval : ((X⊸Y)⊗X) ⊸ Y := uncurry' id
  -- noncomputable
  -- def tpair : X⊸Y⊸X⊗Y := curry' id

  
  -- def assocl : X×(Y×Z) ⊸ (X×Y)×Z := 
  --   let F : X×(Y×Z) ⊸ (X×Y)×Z := pmap ((pmap (fst, (comp' fst snd))), (comp' snd snd))
  --   ⟨λ (x,(y,z)) => ((x,y),z), 
  --    by 
  --      have h : (λ (x,(y,z)) => ((x,y),z)) = F.1 := by simp[pmap, comp', fst, snd]
  --      rw[h]
  --      apply F.2⟩

  -- def assocr : (X×Y)×Z ⊸ X×(Y×Z) := 
  --   let F : (X×Y)×Z ⊸ X×(Y×Z) := pmap ((comp' fst fst), (pmap ((comp' snd fst), snd)))
  --   ⟨λ ((x,y),z) => (x,(y,z)),
  --    by 
  --      have h : (λ ((x,y),z) => (x,(y,z))) = F.1 := by simp[pmap, comp', fst, snd]
  --      rw[h]
  --      apply F.2⟩

  -- @[simp]
  -- theorem assocl_eval (xyz : X×(Y×Z)) : assocl xyz = ((xyz.1,xyz.2.1),xyz.2.2) := rfl

  -- @[simp]
  -- theorem assocr_eval (xyz : (X×Y)×Z) : assocr xyz = (xyz.1.1,(xyz.1.2,xyz.2)) := rfl

  -- noncomputable
  -- def tassocl : X⊗(Y⊗Z) ⊸ (X⊗Y)⊗Z := ⟨λ xyz => 
  --   let ⟨_,x,yz⟩ := xyz.repr
  --   let y := λ i => (yz i).repr.snd.fst
  --   let z := λ i => (yz i).repr.snd.snd
  --   ∑ i j, (x i ⊗ y i j) ⊗ z i j,
  --   sorry_proof⟩

  -- noncomputable
  -- def tassocr : (X⊗Y)⊗Z ⊸ X⊗(Y⊗Z) := ⟨λ xyz => 
  --   let ⟨_,xy,z⟩ := xyz.repr
  --   let x := λ i => (xy i).repr.snd.fst
  --   let y := λ i => (xy i).repr.snd.snd
  --   ∑ i j, x i j ⊗ (y i j ⊗ z i),
  --   sorry_proof⟩

  -- def swap : (X×Y) ⊸ (Y×X) := pmap (snd, fst)

  -- @[simp]
  -- theorem swap_eval (xy : (X×Y)) : swap xy = (xy.2, xy.1) := rfl

  -- noncomputable
  -- def tswap : (X⊗Y) ⊸ (Y⊗X) := ⟨λ xy => 
  --   let ⟨_,x,y⟩ := xy.repr
  --   ∑ i, y i ⊗ x i,
  --   sorry_proof⟩

  -- def rot132 : (X×Y)×Z ⊸ (X×Z)×Y := comp' assocl (comp' (fmap (id, swap)) assocr)

  -- @[simp]
  -- theorem rot132_eval (xyz : (X×Y)×Z) : rot132 xyz = ((xyz.1.1, xyz.2), xyz.1.2) := rfl

  -- noncomputable
  -- def trot132 : (X⊗Y)⊗Z ⊸ (X⊗Z)⊗Y := comp' tassocl (comp' (tfmap id tswap) tassocr)

  -- @[simp]
  -- theorem trot132_eval (x : X) (y : Y) (z : Z) : trot132 ((x⊗y)⊗z) = (x⊗z)⊗y := sorry_proof

  -- -- TODO: This function is perfectly computable, make it so
  -- -- only the proof of linearity goes via noncomputable tensor product
  -- noncomputable
  -- def comp : (Y ⊸ Z) ⊸ (X ⊸ Y) ⊸ (X ⊸ Z) := 
  --   let F₁ : (Y⊸Z)⊗((X⊸Y)⊗X) ⊸ Z := comp' teval (tfmap id teval)
  --   curry' (curry' (comp' F₁ tassocr))


  -- @[simp]
  -- theorem comp_eval (f : Y⊸Z) (g : X ⊸ Y) (x : X) : comp f g x = f (g x) := sorry_proof

  -- -- def const : X⊸Y⊸X := curry' fst

  -- -- @[simp]
  -- -- theorem const_eval (f : Y⊸Z) (g : X ⊸ Y) (x : X) : comp f g x = f (g x) := rfl

  -- noncomputable
  -- def uncurry : (X ⊸ Y ⊸ Z) ⊸ (X⊗Y ⊸ Z) := 
  --   let F : ((X⊸Y⊸Z)⊗X)⊗Y ⊸ Z := comp teval (tfmap teval id)

  --   let G₁ : (X⊗Y ⊸ (X⊸Y⊸Z)⊗(X⊗Y)) ⊸ (X⊗Y ⊸ Z) := comp (comp' F tassocl)
  --   let G₂ : (X⊸Y⊸Z) ⊸ (X⊗Y ⊸ (X⊸Y⊸Z)⊗(X⊗Y)) := tpair
  --   comp' G₁ G₂

  -- -- @[simp]
  -- -- theorem Smooth.uncurry_eval (f : X ⊸ Y ⊸ Z) (xy : X×Y) : Smooth.uncurry f xy = f xy.1 xy.2 := by rfl
  
  -- noncomputable
  -- def curry : (X ⊗ Y ⊸ Z) ⊸ (X ⊸ Y ⊸ Z) := 

  --   let G : ((X⊗Y⊸Z)⊗Y)⊗X ⊸ Z := comp (comp (uncurry' id) (tfmap id tswap)) tassocr

  --   let H : (Y ⊸ (X⊗Y⊸Z)⊗Y)⊗X ⊸ (Y ⊸ ((X⊗Y⊸Z)⊗Y)⊗X) := curry' (comp (tfmap teval id) trot132)

  --   let F₁ : (X⊗Y⊸Z) ⊸ (Y ⊸ (X⊗Y⊸Z)⊗Y) := tpair
  --   let F₂ : (Y ⊸ (X⊗Y⊸Z)⊗Y) ⊸ (X ⊸ (Y ⊸ (X⊗Y⊸Z)⊗Y)⊗X) := tpair
  --   let F₃ : (X ⊸ (Y ⊸ (X⊗Y⊸Z)⊗Y)⊗X) ⊸ (X ⊸ (Y ⊸ ((X⊗Y⊸Z)⊗Y)⊗X)) := comp H

  --   comp (comp (comp G)) (comp F₃ (comp F₂ F₁))

  -- -- @[simp]
  -- -- theorem Smooth.curry_eval (f : X×Y ⊸ Z) (x : X) (y : Y) : Smooth.curry f x y = f (x,y) := by rfl

  -- -- TODO: make it computable
  -- noncomputable 
  -- def prod : (X → Y ⊸ Z) ⊸ (X→Y) ⊸ (X→Z) := 
  --   let F : (X → Y ⊸ Z) ⊸ (X→Y) ⊸ (X → Y ⊸ Z)⊗(X→Y) := tpair
  --   let G₁ : (X → Y ⊸ Z)⊗(X→Y) ⊸ (X → (Y⊸Z)⊗Y) := uncurry tpmap'
  --   let G₂ : (X → (Y⊸Z)⊗Y) ⊸ (X→Z) := comp'' teval
    
  --   comp (comp (comp G₂ G₁)) F

  -- @[simp]
  -- theorem prod_eval (f : X → Y ⊸ Z) : prod f (λ _ => y) x = f x y := sorry_proof

  -- -- def scomb : (X⊸Y⊸Z) ⊸ (X⊸Y) ⊸ X ⊸ Z := 
  -- --   let F₁ : (X⊸Y⊸Z)⊗(X⊸Y)⊗X ⊸ (X⊗Y⊸Z)⊗(X⊗Y) := tfmap uncurry (tpmap snd teval)
  -- --   comp (curry) (curry (comp eval F₁))


  -- -- variable {ι κ : Type} {E F G : ι → Type} {E' : κ → Type} [∀ i, Vec (E i)] [∀ i, Vec (F i)] [∀ i, Vec (G i)] [∀ j, Vec (E' j)]
  -- -- instance  [∀ i, Vec (F i)] : Vec ((i : ι) → (F i)) := sorry

  -- -- def Smooth.pmapDep : ((i : ι)→(E i)) ⊸ ((i : ι)→(F i)) ⊸ ((i : ι)→(E i)×(F i)) := ⟨λ f => ⟨λ g => λ x => (f x, g x), sorry⟩, sorry⟩
  -- -- def Smooth.fmapDep : ((i : ι)→(E i)) ⊸ ((j : κ)→(E' j)) ⊸ ((ij : (ι×κ))→(E ij.1)×(E' ij.2)) := ⟨λ f => ⟨λ g => λ (i,j) => (f i, g j), sorry⟩, sorry⟩
  -- -- def Smooth.prodDep : ((i : ι) → E i ⊸ F i) ⊸ ((i : ι) → E i) ⊸ ((i : ι) → F i) := sorry 


  -- end Linear

