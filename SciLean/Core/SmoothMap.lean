-- import SciLean.Core.Attributes
import SciLean.Mathlib.Convenient.Basic
import SciLean.Data.Prod

import SciLean.Core.Tactic.FunctionTransformation.Init

import Mathlib.Data.FunLike.Basic

namespace SciLean

@[fun_prop_def]
structure IsSmooth {X Y : Type _} [Vec X] [Vec Y] (f : X → Y) : Prop where
  isSmooth : Mathlib.Convenient.is_smooth f

structure SmoothMap (X Y : Type _) [Vec X] [Vec Y] where
  toFun : X → Y 
  isSmooth_toFun : IsSmooth toFun := by infer_instance

/-- `X ~~> Y` is the space of all smooth maps between `X` and `Y`.

The notation `X ⟿ Y` is prefered, but this fixes pure ASCII equivalent. -/
infixr:25 " ~~> " => SmoothMap 

/-- `X ⟿ Y` is the space of all smooth maps between `X` and `Y`. 

Can be also written as `X ~~> Y` -/
infixr:25 " ⟿ " => SmoothMap

-- Lambda notation
open Lean.TSyntax.Compat in
macro "λ"   xs:Lean.explicitBinders " ⟿ " b:term : term =>
  Lean.expandExplicitBinders `SciLean.SmoothMap.mk xs b
open Lean.TSyntax.Compat in
macro "fun"   xs:Lean.explicitBinders " ⟿ " b:term : term =>
  Lean.expandExplicitBinders `SciLean.SmoothMap.mk xs b


class SmoothMapClass (F : Type _) (X Y : outParam <| Type _) [Vec X] [Vec Y]
  extends FunLike F X fun _ => Y where
  map_isSmooth (f : F) : IsSmooth f


export SmoothMapClass (map_isSmooth)

attribute [fun_prop] map_isSmooth

section SmoothMapClass

  variable {F X Y : Type _} [Vec X] [Vec Y] [SmoothMapClass F X Y]

  instance : CoeTC F (X ⟿ Y) :=
    ⟨fun f =>
      { toFun := f
        isSmooth_toFun := map_isSmooth f }⟩

end SmoothMapClass

namespace SmoothMap

  -- The following is heavily inspired by ContinuousMap

  variable {X Y Z W : Type _} [Vec X] [Vec Y] [Vec Z] [Vec W]

  instance : SmoothMapClass (X⟿Y) X Y where
    map_isSmooth f := f.isSmooth_toFun
    coe f := f.toFun
    coe_injective' := sorry_proof
    
  @[simp]
  theorem toFun_eq_coe {f : X ⟿ Y} : f.toFun = (f : X → Y) :=
    rfl

  def Simps.apply (f : X ⟿ Y) : X → Y := f

  initialize_simps_projections SmoothMap (toFun → apply)

  @[simp]
  protected theorem coe_coe {F : Type} [SmoothMapClass F X Y] (f : F) : ⇑(f : X ⟿ Y) = f :=
    rfl

  @[ext]
  theorem ext {f g : X ⟿ Y} (h : ∀ x, f x = g x) : f = g :=
    FunLike.ext _ _ h

  @[fun_prop]
  theorem isSmooth_set_coe (s : Set (X⟿Y)) (f : s) : IsSmooth (f : X → Y) :=
    map_isSmooth f.1

  @[simp]
  theorem coe_mk (f : X → Y) (h : IsSmooth f) : ⇑(⟨f, h⟩ : X ⟿ Y) = f :=
    rfl

  @[simp]
  theorem eta (f : X ⟿ Y)
      : (λ (x : X) ⟿ f x) = f := by rfl; done

  protected def id : X ⟿ X :=
    SmoothMap.mk (λ x => x) sorry

  @[simp]
  theorem coe_id : ⇑(SmoothMap.id : X ⟿ X) = _root_.id := 
    rfl

  @[simp]
  theorem id_apply (x : X) : SmoothMap.id x = x :=
    rfl

  ------------------------------------------------------------------------------
  -- X ⟿ Y is vector space 
  ------------------------------------------------------------------------------

  theorem show_smoothness_via {X Y} [Vec X] [Vec Y] {f : X → Y} (g : X ⟿ Y) : (f = g) → IsSmooth f :=
  by
    intro p
    have q : f = g := by apply p
    rw[q]; infer_instance

  variable {α : Type}

  private def comp' : (Y ⟿ Z) → (X ⟿ Y) → (X⟿Z) := λ f g =>
    SmoothMap.mk (λ x => f (g x)) sorry

  private def prodMap' : (X⟿Y) → (X⟿Z) → (X ⟿ Y×Z) := λ f g =>
    SmoothMap.mk (λ x => (f x, g x)) sorry

  private def prodMap'' : (α→X) × (α→Y) ⟿ (α → X×Y) :=
    SmoothMap.mk (λ (x,y) a => (x a, y a)) sorry

  private def const' : X→Y⟿X := λ x =>
    SmoothMap.mk (λ y => x) sorry

  @[simp] private theorem comp'_eval (f : Y ⟿ Z) (g : X⟿Y) (x : X) : comp' f g x = f (g x) := by simp[comp']
  @[simp] private theorem prodMap'_eval (f : X ⟿ Y) (g : X⟿Z) (x : X) : prodMap' f g x = (f x, g x) := by simp[prodMap']
  @[simp] private theorem SmoothMap.prodMap''_eval (xy : (α→X) × (α→Y)) : SmoothMap.prodMap'' xy = λ a => (xy.1 a , xy.2 a) := by simp[SmoothMap.prodMap'']
  @[simp] private theorem SmoothMap.const'_eval (x : X) (y : Y) : SmoothMap.const' x y = x := by simp[SmoothMap.const']

  def neg : X ⟿ X := SmoothMap.mk (λ x => -x) sorry
  private def add' : X×X ⟿ X := SmoothMap.mk (λ (x,y) => x+y) sorry
  private def sub' : X×X ⟿ X := SmoothMap.mk (λ (x,y) => x-y) sorry
  private def smul' : ℝ×X ⟿ X := SmoothMap.mk (λ (r,x) => r•x) sorry
  private def mul' : ℝ×ℝ ⟿ ℝ := SmoothMap.mk (λ (x,y) => x*y) sorry

  instance : Neg (X⟿Y) := ⟨λ f => SmoothMap.mk (λ x => -f x) 
    (show_smoothness_via (comp' neg f) (by ext; simp[neg]))⟩

  instance : Add (X⟿Y) := ⟨λ f g => SmoothMap.mk (λ x => f x + g x)
    (show_smoothness_via (comp' add' (prodMap' f g)) (by ext; simp[add']))⟩

  instance : Sub (X⟿Y) := ⟨λ f g => SmoothMap.mk (λ x => f x - g x)
    (show_smoothness_via (comp' sub' (prodMap' f g)) (by ext; simp[sub']))⟩

  instance : Mul (X⟿ℝ) := ⟨λ f g => SmoothMap.mk (λ x => f x * g x)
    (show_smoothness_via (comp' mul' (prodMap' f g)) (by ext; simp[mul']))⟩

  instance : SMul ℝ (X⟿Y) := ⟨λ r f => SmoothMap.mk (λ x => r • f x)
    (show_smoothness_via (comp' smul' (prodMap' (const' r) f)) (by ext; simp[smul']))⟩

  instance : HMul (X⟿ℝ) (X⟿Y) (X⟿Y) := ⟨λ f g => SmoothMap.mk (λ x => f x • g x)
    (show_smoothness_via (comp' smul' (prodMap' f g)) (by ext; simp[smul']))⟩
 
  instance : Zero (X ⟿ Y) := ⟨const' 0⟩
  instance [One Y] : One (X ⟿ Y) := ⟨const' 1⟩

  -- !!!THIS USES SORRY!!!
  instance : Vec (X ⟿ Y) := Vec.mkSorryProofs

  ------------------------------------------------------------------------------
  -- Basic combinators like const, comp, curry, uncurry, prodMk, prodMap, pi
  ------------------------------------------------------------------------------

  -- const --
  -----------
  private def const (Y : Type _) [Vec Y] : X ⟿ Y ⟿ X := 
    SmoothMap.mk (λ x => 
      SmoothMap.mk (λ y => x) 
        sorry)
      sorry

  @[simp]
  private theorem coe_const (x : X) : ⇑(const Y x) = Function.const Y x :=
    rfl

  @[simp]
  private theorem const_apply (x : X) (y : Y) : const Y x y = x :=
    rfl
  
  -- comp --
  ----------
  def comp : (Y⟿Z)⟿(X⟿Y)⟿X⟿Z := 
    SmoothMap.mk (λ f : Y⟿Z => 
      SmoothMap.mk (λ g : X⟿Y => 
        SmoothMap.mk (λ x : X => f (g x)) 
        sorry)
      sorry)
    sorry

  @[simp]
  theorem coe_comp (f : Y ⟿ Z) (g : X ⟿ Y) : ⇑(comp f g) = f ∘ g := 
    rfl

  @[simp] 
  theorem comp_apply (f : Y ⟿ Z) (g : X ⟿ Y) (x : X) : comp f g x = f (g x) :=
    rfl

  @[simp] 
  theorem comp_assoc (f : Y ⟿ Z) (g : X ⟿ Y) (h : W ⟿ X) : 
      comp (comp f g) h = comp f (comp g h) :=
    rfl

  -- forget --
  -----------
  def forget : (X⟿Y)⟿(X→Y) := SmoothMap.mk (λ f x => f x) sorry

  @[simp] theorem forget_apply (f : X⟿Y) : forget f = (f : X → Y) := by rfl


  section Prod

    def prodMk (f : X ⟿ Y) (g : X ⟿ Z) : X ⟿ Y×Z :=
      SmoothMap.mk (λ x => (f x, g x)) sorry

    @[simps]
    def prodMap (f : X ⟿ Y) (g : W ⟿ Z) : X×W⟿Y×Z :=
      SmoothMap.mk (λ (x,w) => (f x, g w)) sorry

    @[simp]
    theorem prod_eval (f : X ⟿ Y) (g : X ⟿ Z) (x : X) : 
        (prodMk f g) x = (f x, g x) :=
      rfl

    def fst : X×Y ⟿ X := SmoothMap.mk (λ (x,y) => x) sorry
    def snd : X×Y ⟿ Y := SmoothMap.mk (λ (x,y) => y) sorry

    @[simp] theorem fst_apply (xy : X×Y) : fst xy = xy.1 := by rfl
    @[simp] theorem snd_apply (xy : X×Y) : snd xy = xy.2 := by rfl

  end Prod

  section Pi

    def pi (f : α → X ⟿ Y) : X ⟿ (α → Y) := 
      SmoothMap.mk (λ x a => f a x) sorry

    @[simp]
    theorem pi_eval (f : α → X ⟿ Y) (x : X) : pi f x = fun a => f a x :=
      rfl

    def proj : α → (α → X) ⟿ X := λ a => SmoothMap.mk (λ f => f a) sorry

    @[simp] theorem proj_apply (a : α) (f : α → X) : proj a f = f a := by simp[proj]

  end Pi

  -- variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

  private def curry' (f : X×Y ⟿ Z) : (X ⟿ Y ⟿ Z) := 
    SmoothMap.mk (λ x => 
      SmoothMap.mk (λ y => f (x,y))
      sorry)
    sorry

  private def uncurry' (f : X ⟿ Y ⟿ Z) : (X×Y ⟿ Z) :=
    SmoothMap.mk (λ (x,y) => f x y) sorry

  private def forallMap'  (f : α → X⟿Y) : (α → X) ⟿ (α → Y) :=
    SmoothMap.mk (λ x a => f a (x a)) sorry


  @[simp] private theorem curry'_apply (f : X×Y ⟿ Z) (x y) : curry' f x y = f (x,y) := by simp[curry']
  @[simp] private theorem uncurry'_apply (f : X⟿ Y ⟿ Z) (xy : X×Y) : uncurry' f xy = f xy.1 xy.2:= by simp[uncurry']
  @[simp] private theorem forallMap'_apply (f : α→X⟿Y) (g : α→X) (a : α) : forallMap' f g a = f a (g a) := by simp[forallMap']


  -- def id : X ⟿ X := SmoothMap.mk (λ x => x) sorry

  -- def const (α : Type) : X⟿(α→X) := SmoothMap.mk (λ x a => x) sorry


  -- @[simp] theorem id_apply (x : X) : id x = x := by simp[id]
  -- @[simp] theorem const_apply (x : X) : const α x = λ _ => x := by simp[const]


  def pair : X⟿Y⟿X×Y := 
    SmoothMap.mk (λ x => 
      SmoothMap.mk (λ y => (x,y))
      (show_smoothness_via (curry' SmoothMap.id x) (by funext x; simp)))
    (show_smoothness_via (curry' SmoothMap.id) (by funext y; simp[curry']))

  def swap : X×Y⟿Y×X := 
    SmoothMap.mk (λ (x,y) => (y,x))
      (show_smoothness_via (prodMap' snd fst) (by funext; simp))


  @[simp] theorem pair_apply (x : X) (y : Y) : pair x y = (x,y) := by simp[pair]
  @[simp] theorem swap_apply (xy : X×Y) : swap xy = (xy.2,xy.1) := by simp[swap]


  def eval : X⟿(X⟿Y)⟿Y := 
    SmoothMap.mk (λ x : X => 
      SmoothMap.mk (λ f : X⟿Y => f x)
      (show_smoothness_via (curry' (comp' (uncurry' SmoothMap.id) swap) x) (by ext; simp)))
    (show_smoothness_via (curry' (comp' (uncurry' SmoothMap.id) swap)) (by ext; simp))

  def assocl : X×(Y×Z) ⟿ (X×Y)×Z := 
    SmoothMap.mk (λ (x,y,z) => ((x,y),z))
      (show_smoothness_via (prodMap' (prodMap' fst (comp' fst snd))  (comp' snd snd)) (by funext; simp))

  def assocr : (X×Y)×Z ⟿ X×(Y×Z) := 
    SmoothMap.mk (λ ((x,y),z) => (x,y,z))
      (show_smoothness_via (prodMap' (comp' fst fst) (prodMap' (comp' snd fst) snd)) (by funext; simp))


  @[simp] theorem eval_apply (x : X) (f : X⟿Y) : eval x f = f x := by simp[eval]
  @[simp] theorem assocl_apply (xyz : X×(Y×Z)) : assocl xyz = ((xyz.1, xyz.2.1),xyz.2.2) := by simp[assocl]
  @[simp] theorem assocr_apply (xyz : (X×Y)×Z) : assocr xyz = (xyz.1.1, (xyz.1.2,xyz.2)) := by simp[assocr]


  -- def comp : (Y⟿Z)⟿(X⟿Y)⟿X⟿Z := 
  --   SmoothMap.mk (λ f : Y⟿Z => 
  --     SmoothMap.mk (λ g : X⟿Y => 
  --       SmoothMap.mk (λ x : X => f (g x)) 
  --       (show_smoothness_via (comp' (f) (g)) (by ext; simp)))
  --     (show_smoothness_via (curry' (comp' (f) (uncurry' (SmoothMap.id (X:=X⟿Y))))) (by ext; simp)))
  --   (show_smoothness_via (
  --     let F : (Y⟿Z)×(X⟿Y)×X⟿Z := comp' (uncurry' SmoothMap.id) (prodMap' (fst) (comp' (uncurry' (SmoothMap.id (X:=X⟿Y))) (snd)))
  --     curry' (curry' (comp' F (assocr)))) 
  --     (by ext; simp))

  -- def prodMap : (X⟿Y)⟿(X⟿Z)⟿X⟿Y×Z :=
  --   SmoothMap.mk (λ f => 
  --     SmoothMap.mk (λ g => 
  --       SmoothMap.mk (λ x => (f x, g x))
  --       (show_smoothness_via (prodMap' f g) (by funext; simp)))
  --     (show_smoothness_via (curry' (comp' swap (prodMap' (uncurry' SmoothMap.id) (comp' f snd)))) (by funext g; simp[comp',curry'])))
  --   (show_smoothness_via (
  --     let F : (X⟿Y)×(X⟿Z)×X ⟿ Y×Z := comp' 
  --       (prodMap' (comp' (uncurry' SmoothMap.id) fst) (comp' (uncurry' SmoothMap.id) snd)) 
  --       (prodMap' (prodMap' fst (comp' snd snd)) (prodMap' (comp' fst snd) (comp' snd snd)))
  --     curry' (curry' (comp' F (assocr))))
  --     (by funext; simp[comp']; simp[curry']))


  -- @[simp] theorem comp_apply (f : Y⟿Z) (g : X⟿Y) : comp f g = comp' f g := by simp[comp,comp']
  -- @[simp] theorem prodMap_apply (f : Y⟿Z) (g : X⟿Y) (x : X) : comp f g x = f (g x) := by simp[comp]


  def curry : (X×Y⟿Z)⟿X⟿Y⟿Z := 
    SmoothMap.mk (λ f => 
      SmoothMap.mk (λ x => 
        SmoothMap.mk (λ y => f (x,y)) 
        (show_smoothness_via (curry' f x) (by ext; simp)))
      (show_smoothness_via (curry' f) (by ext; simp)))
    (show_smoothness_via (
      let F : ((X×Y⟿Z)×X)×Y⟿Z := comp' (uncurry' SmoothMap.id) assocr
      curry' (curry' F)
      ) (by ext; simp))

  def uncurry : (X⟿Y⟿Z)⟿X×Y⟿Z := 
    SmoothMap.mk (λ f => 
      SmoothMap.mk (λ xy => f xy.1 xy.2)
      (show_smoothness_via (uncurry' f) (by ext; simp)))
    (show_smoothness_via (
      let F : ((X⟿Y⟿Z)×X)×Y⟿Z := comp' (uncurry' SmoothMap.id) (prodMap' (comp' (uncurry' SmoothMap.id) fst) snd)
      (curry' (comp' F assocl))
      ) (by ext; simp))

  def forallMap : (α → X⟿Y) ⟿ (α → X) ⟿ (α → Y) :=
    SmoothMap.mk (λ f => 
      SmoothMap.mk (λ x a => f a (x a)) 
      (show_smoothness_via (forallMap' f) (by ext; simp)))
    (show_smoothness_via (
      let F : (α → (X⟿Y))×(α → X) ⟿ _ := prodMap'' |> comp' (forallMap' (λ _ => uncurry' SmoothMap.id))
      curry' F
    ) (by ext f g a; simp[curry']))


  @[simp] theorem curry_apply (f : X×Y⟿Z) : curry f = curry' f := by simp[curry,curry']
  @[simp] theorem uncurry_apply (f : X⟿Y⟿Z) : uncurry f = uncurry' f := by simp[uncurry,uncurry']
  @[simp] theorem forallMap_apply (f : α→X⟿Y) : forallMap f = forallMap' f := by simp[forallMap, forallMap']


  -- variable {ι κ : Type} {E F G : ι → Type} {E' : κ → Type} [∀ i, Vec (E i)] [∀ i, Vec (F i)] [∀ i, Vec (G i)] [∀ j, Vec (E' j)]

  -- def pmapDep : ((i : ι)→(E i)) ⟿ ((i : ι)→(F i)) ⟿ ((i : ι)→(E i)×(F i)) := ⟨λ f => ⟨λ g => λ x => (f x, g x), sorry⟩, sorry⟩
  -- def fmapDep : ((i : ι)→(E i)) ⟿ ((j : κ)→(E' j)) ⟿ ((ij : (ι×κ))→(E ij.1)×(E' ij.2)) := ⟨λ f => ⟨λ g => λ (i,j) => (f i, g j), sorry⟩, sorry⟩
  -- def prodDep : ((i : ι) → E i ⟿ F i) ⟿ ((i : ι) → E i) ⟿ ((i : ι) → F i) := sorry 


