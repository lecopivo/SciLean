import SciLean.Core.Attributes
import SciLean.Mathlib.Convenient.Basic
import SciLean.Data.Prod

namespace SciLean

  class IsSmoothT {X Y : Type} [Vec X] [Vec Y] (f : X → Y) : Prop where
    is_smooth : Mathlib.Convenient.is_smooth f

  class IsSmooth {X Y} [Vec X] [Vec Y] (f : X → Y) extends IsSmoothT f : Prop

  class IsSmoothN {X Y : Type} {Xs Y' : Type} [Vec Xs] [Vec Y'] 
   (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] : Prop where
   is_smooth : IsSmoothT (uncurryN n f) 


  structure SmoothMap (X Y : Type) [Vec X] [Vec Y] where
    val : X → Y 
    [property : IsSmoothT val] 

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


  instance {X Y} [Vec X] [Vec Y] : CoeFun (X⟿Y) (λ _ => X→Y) := ⟨λ f => f.1⟩

  instance SmoothMap.val.arg_x.isSmooth {X Y} [Vec X] [Vec Y] (f : X ⟿ Y)
    : IsSmoothT f.1 := f.2

  abbrev SmoothMap.mk' {X Y} [Vec X] [Vec Y] (f : X → Y) (_ : IsSmoothT f) : X⟿Y := λ x ⟿ f x

  @[ext] 
  theorem SmoothMap.ext {X Y} [Vec X] [Vec Y] (f g : X ⟿ Y) : (∀ x, f x = g x) → f = g := by sorry

  @[simp, diff_simp]
  theorem SmoothMap.eta_reduction {X Y} [Vec X] [Vec Y] (f : X ⟿ Y)
      : (λ (x : X) ⟿ f x) = f := by rfl; done

  theorem show_smoothness_via {X Y} [Vec X] [Vec Y] {f : X → Y} (g : X ⟿ Y) : (∀ x, f x = g x) → IsSmoothT f :=
  by
    intro p
    have q : f = g := by ext; apply p
    rw[q]; infer_instance

  variable {X Y Z} [Vec X] [Vec Y] [Vec Z] {α : Type}

  def Smooth.comp' : (Y ⟿ Z) → (X ⟿ Y) → (X⟿Z) := λ f g =>
    SmoothMap.mk (property := sorry) λ x => f (g x)

  def Smooth.prodMap' : (X⟿Y) → (X⟿Z) → (X ⟿ Y×Z) := λ f g =>
    SmoothMap.mk (property := sorry) λ x => (f x, g x)

  def Smooth.prodMap'' : (α→X) × (α→Y) ⟿ (α → X×Y) :=
    SmoothMap.mk (property := sorry) λ (x,y) a => (x a, y a)

  def Smooth.const' : X→Y⟿X := λ x =>
    SmoothMap.mk (property := sorry) λ y => x

  @[simp] theorem Smooth.comp'_eval (f : Y ⟿ Z) (g : X⟿Y) (x : X) : Smooth.comp' f g x = f (g x) := by simp[Smooth.comp']
  @[simp] theorem Smooth.prodMap'_eval (f : X ⟿ Y) (g : X⟿Z) (x : X) : Smooth.prodMap' f g x = (f x, g x) := by simp[Smooth.prodMap']
  @[simp] theorem Smooth.prodMap''_eval (xy : (α→X) × (α→Y)) : Smooth.prodMap'' xy = λ a => (xy.1 a , xy.2 a) := by simp[Smooth.prodMap'']
  @[simp] theorem Smooth.const'_eval (x : X) (y : Y) : Smooth.const' x y = x := by simp[Smooth.const']

  def Smooth.neg : X ⟿ X := SmoothMap.mk' (λ x => -x) sorry
  def Smooth.add' : X×X ⟿ X := SmoothMap.mk' (λ (x,y) => x+y) sorry
  def Smooth.sub' : X×X ⟿ X := SmoothMap.mk' (λ (x,y) => x-y) sorry
  def Smooth.smul' : ℝ×X ⟿ X := SmoothMap.mk' (λ (r,x) => r*x) sorry
  def Smooth.mul' : ℝ×ℝ ⟿ ℝ := SmoothMap.mk' (λ (x,y) => x*y) sorry

  open Smooth

  instance : Neg (X⟿Y) := ⟨λ f => SmoothMap.mk' (λ x => -f x) 
    (show_smoothness_via (comp' neg f) (by ext; simp[neg]))⟩

  instance : Add (X⟿Y) := ⟨λ f g => SmoothMap.mk' (λ x => f x + g x)
    (show_smoothness_via (comp' add' (prodMap' f g)) (by ext; simp[add']))⟩

  instance : Sub (X⟿Y) := ⟨λ f g => SmoothMap.mk' (λ x => f x - g x)
    (show_smoothness_via (comp' sub' (prodMap' f g)) (by ext; simp[sub']))⟩

  instance : Mul (X⟿ℝ) := ⟨λ f g => SmoothMap.mk' (λ x => f x * g x)
    (show_smoothness_via (comp' mul' (prodMap' f g)) (by ext; simp[mul']))⟩

  instance : HMul ℝ (X⟿Y) (X⟿Y) := ⟨λ r f => SmoothMap.mk' (λ x => r * f x)
    (show_smoothness_via (comp' smul' (prodMap' (const' r) f)) (by ext; simp[smul']))⟩

  instance : HMul (X⟿ℝ) (X⟿Y) (X⟿Y) := ⟨λ f g => SmoothMap.mk' (λ x => f x * g x)
    (show_smoothness_via (comp' smul' (prodMap' f g)) (by ext; simp[smul']))⟩
 
  instance : Zero (X ⟿ Y) := ⟨const' 0⟩
  instance [One Y] : One (X ⟿ Y) := ⟨const' 1⟩

  -- !!!THIS USES SORRY!!!
  instance : Vec (X ⟿ Y) := Vec.mkSorryProofs

  --------------------------------------------------------------------

  namespace Smooth

  variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

  def curry' (f : X×Y ⟿ Z) : (X ⟿ Y ⟿ Z) := 
    SmoothMap.mk' (λ x => 
      SmoothMap.mk' (λ y => f (x,y))
      sorry)
    sorry

  def uncurry' (f : X ⟿ Y ⟿ Z) : (X×Y ⟿ Z) :=
    SmoothMap.mk' (λ (x,y) => f x y) sorry

  def forallMap'  (f : α → X⟿Y) : (α → X) ⟿ (α → Y) :=
    SmoothMap.mk' (λ x a => f a (x a)) sorry


  @[simp] theorem curry'_eval (f : X×Y ⟿ Z) (x y) : curry' f x y = f (x,y) := by simp[curry']
  @[simp] theorem uncurry'_eval (f : X⟿ Y ⟿ Z) (xy : X×Y) : uncurry' f xy = f xy.1 xy.2:= by simp[uncurry']
  @[simp] theorem forallMap'_eval (f : α→X⟿Y) (g : α→X) (a : α) : forallMap' f g a = f a (g a) := by simp[forallMap']


  def id : X ⟿ X := SmoothMap.mk' (λ x => x) sorry
  def fst : X×Y ⟿ X := SmoothMap.mk' (λ (x,y) => x) sorry
  def snd : X×Y ⟿ Y := SmoothMap.mk' (λ (x,y) => y) sorry
  def forget : (X⟿Y)⟿(X→Y) := SmoothMap.mk' (λ f x => f x) sorry
  def proj : α → (α → X) ⟿ X := λ a => SmoothMap.mk' (λ f => f a) sorry
  def const (α : Type) : X⟿(α→X) := SmoothMap.mk' (λ x a => x) sorry


  @[simp] theorem id_eval (x : X) : id x = x := by simp[id]
  @[simp] theorem fst_eval (xy : X×Y) : fst xy = xy.1 := by simp[fst]
  @[simp] theorem snd_eval (xy : X×Y) : snd xy = xy.2 := by simp[snd]
  @[simp] theorem forget_eval (f : X⟿Y) : forget f = f.1 := by simp[forget]
  @[simp] theorem proj_eval (a : α) (f : α → X) : proj a f = f a := by simp[proj]
  @[simp] theorem const_eval (x : X) : const α x = λ _ => x := by simp[const]


  def pair : X⟿Y⟿X×Y := 
    SmoothMap.mk' (λ x => 
      SmoothMap.mk' (λ y => (x,y))
      (show_smoothness_via (curry' id x) (by ext; simp)))
    (show_smoothness_via (curry' id) (by ext; simp))

  def swap : X×Y⟿Y×X := 
    SmoothMap.mk' (λ (x,y) => (y,x))
      (show_smoothness_via (prodMap' snd fst) (by ext; simp))


  @[simp] theorem pair_eval (x : X) (y : Y) : pair x y = (x,y) := by simp[pair]
  @[simp] theorem swap_eval (xy : X×Y) : swap xy = (xy.2,xy.1) := by simp[swap]


  def eval : X⟿(X⟿Y)⟿Y := 
    SmoothMap.mk' (λ x : X => 
      SmoothMap.mk' (λ f : X⟿Y => f x)
      (show_smoothness_via (curry' (comp' (uncurry' id) swap) x) (by ext; simp)))
    (show_smoothness_via (curry' (comp' (uncurry' id) swap)) (by ext; simp))

  def assocl : X×(Y×Z) ⟿ (X×Y)×Z := 
    SmoothMap.mk' (λ (x,y,z) => ((x,y),z))
      (show_smoothness_via (prodMap' (prodMap' fst (comp' fst snd))  (comp' snd snd)) (by ext; simp))

  def assocr : (X×Y)×Z ⟿ X×(Y×Z) := 
    SmoothMap.mk' (λ ((x,y),z) => (x,y,z))
      (show_smoothness_via (prodMap' (comp' fst fst) (prodMap' (comp' snd fst) snd)) (by ext; simp))


  @[simp] theorem eval_eval (x : X) (f : X⟿Y) : eval x f = f x := by simp[eval]
  @[simp] theorem assocl_eval (xyz : X×(Y×Z)) : assocl xyz = ((xyz.1, xyz.2.1),xyz.2.2) := by simp[assocl]
  @[simp] theorem assocr_eval (xyz : (X×Y)×Z) : assocr xyz = (xyz.1.1, (xyz.1.2,xyz.2)) := by simp[assocr]


  def comp : (Y⟿Z)⟿(X⟿Y)⟿X⟿Z := 
    SmoothMap.mk' (λ f : Y⟿Z => 
      SmoothMap.mk' (λ g : X⟿Y => 
        SmoothMap.mk' (λ x : X => f (g x)) 
        (show_smoothness_via (comp' (f) (g)) (by ext; simp)))
      (show_smoothness_via (curry' (comp' (f) (uncurry' (id (X:=X⟿Y))))) (by ext; simp)))
    (show_smoothness_via (
      let F : (Y⟿Z)×(X⟿Y)×X⟿Z := comp' (uncurry' id) (prodMap' (fst) (comp' (uncurry' (id (X:=X⟿Y))) (snd)))
      curry' (curry' (comp' F (assocr)))) 
      (by ext; simp))

  def prodMap : (X⟿Y)⟿(X⟿Z)⟿X⟿Y×Z :=
    SmoothMap.mk' (λ f => 
      SmoothMap.mk' (λ g => 
        SmoothMap.mk' (λ x => (f x, g x))
        (show_smoothness_via (prodMap' f g) (by ext; simp)))
      (show_smoothness_via (curry' (comp' swap (prodMap' (uncurry' id) (comp' f snd)))) (by ext; simp)))
    (show_smoothness_via (
      let F : (X⟿Y)×(X⟿Z)×X ⟿ Y×Z := comp' 
        (prodMap' (comp' (uncurry' id) fst) (comp' (uncurry' id) snd)) 
        (prodMap' (prodMap' fst (comp' snd snd)) (prodMap' (comp' fst snd) (comp' snd snd)))
      curry' (curry' (comp' F (assocr))))
      (by ext; simp))


  @[simp] theorem comp_eval (f : Y⟿Z) (g : X⟿Y) : comp f g = comp' f g := by simp[comp,comp']
  @[simp] theorem prodMap_eval (f : Y⟿Z) (g : X⟿Y) (x : X) : comp f g x = f (g x) := by simp[comp]


  def curry : (X×Y⟿Z)⟿X⟿Y⟿Z := 
    SmoothMap.mk' (λ f => 
      SmoothMap.mk' (λ x => 
        SmoothMap.mk' (λ y => f (x,y)) 
        (show_smoothness_via (curry' f x) (by ext; simp)))
      (show_smoothness_via (curry' f) (by ext; simp)))
    (show_smoothness_via (
      let F : ((X×Y⟿Z)×X)×Y⟿Z := comp' (uncurry' id) assocr
      curry' (curry' F)
      ) (by ext; simp))

  def uncurry : (X⟿Y⟿Z)⟿X×Y⟿Z := 
    SmoothMap.mk' (λ f => 
      SmoothMap.mk' (λ xy => f xy.1 xy.2)
      (show_smoothness_via (uncurry' f) (by ext; simp)))
    (show_smoothness_via (
      let F : ((X⟿Y⟿Z)×X)×Y⟿Z := comp' (uncurry' id) (prodMap' (comp' (uncurry' id) fst) snd)
      (curry' (comp' F assocl))
      ) (by ext; simp))

  def forallMap : (α → X⟿Y) ⟿ (α → X) ⟿ (α → Y) :=
    SmoothMap.mk' (λ f => 
      SmoothMap.mk' (λ x a => f a (x a)) 
      (show_smoothness_via (forallMap' f) (by ext; simp)))
    (show_smoothness_via (
      let F : (α → (X⟿Y))×(α → X) ⟿ _ := prodMap'' |> comp' (forallMap' (λ _ => uncurry' id))
      curry' F
    ) (by ext f g a; simp[curry']))


  @[simp] theorem curry_eval (f : X×Y⟿Z) : curry f = curry' f := by simp[curry,curry']
  @[simp] theorem uncurry_eval (f : X⟿Y⟿Z) : uncurry f = uncurry' f := by simp[uncurry,uncurry']
  @[simp] theorem forallMap_eval (f : α→X⟿Y) : forallMap f = forallMap' f := by simp[forallMap, forallMap']


  -- variable {ι κ : Type} {E F G : ι → Type} {E' : κ → Type} [∀ i, Vec (E i)] [∀ i, Vec (F i)] [∀ i, Vec (G i)] [∀ j, Vec (E' j)]

  -- def pmapDep : ((i : ι)→(E i)) ⟿ ((i : ι)→(F i)) ⟿ ((i : ι)→(E i)×(F i)) := ⟨λ f => ⟨λ g => λ x => (f x, g x), sorry⟩, sorry⟩
  -- def fmapDep : ((i : ι)→(E i)) ⟿ ((j : κ)→(E' j)) ⟿ ((ij : (ι×κ))→(E ij.1)×(E' ij.2)) := ⟨λ f => ⟨λ g => λ (i,j) => (f i, g j), sorry⟩, sorry⟩
  -- def prodDep : ((i : ι) → E i ⟿ F i) ⟿ ((i : ι) → E i) ⟿ ((i : ι) → F i) := sorry 


  end Smooth

