import SciLean.Mathlib.Convenient.Basic

namespace SciLean

  structure SmoothMap (X Y : Type) [Vec X] [Vec Y] where
    val : X → Y 
    is_smooth : Mathlib.Convenient.is_smooth val

  /-- `X ~~> Y` is the space of all smooth maps between `X` and `Y`.

  The notation `X ⟿ Y` is prefered, but this fixes pure ASCII equivalent. -/
  infixr:25 " ~~> " => SmoothMap 

  /-- `X ⟿ Y` is the space of all smooth maps between `X` and `Y` -/
  infixr:25 " ⟿ " => SmoothMap

  variable {X Y} [Vec X] [Vec Y]

  instance : Neg (X⟿Y) := ⟨λ f   => ⟨-f.1, sorry⟩⟩
  instance : Add (X⟿Y) := ⟨λ f g => ⟨f.1 + g.1, sorry⟩⟩
  instance : Sub (X⟿Y) := ⟨λ f g => ⟨f.1 - g.1, sorry⟩⟩
  instance : Mul (X⟿ℝ) := ⟨λ f g => ⟨f.1 * g.1, sorry⟩⟩
  instance : HMul ℝ (X⟿Y) (X⟿Y) := ⟨λ r f => ⟨r * f.1, sorry⟩⟩
  instance : HMul (X⟿ℝ) (X⟿Y) (X⟿Y) := ⟨λ g f => ⟨λ x => g.1 x * f.1 x, sorry⟩⟩
 
  instance : Zero (X ⟿ Y) := ⟨⟨0, sorry⟩⟩
  instance [One Y] : One (X ⟿ Y) := ⟨⟨1, sorry⟩⟩

  instance : AddSemigroup (X ⟿ Y) := AddSemigroup.mk sorry
  instance : AddMonoid (X ⟿ Y)    := AddMonoid.mk sorry sorry nsmulRec sorry sorry
  instance : SubNegMonoid (X ⟿ Y) := SubNegMonoid.mk sorry zsmulRec sorry sorry sorry
  instance : AddGroup (X ⟿ Y)     := AddGroup.mk sorry
  instance : AddCommGroup (X ⟿ Y) := AddCommGroup.mk sorry

  instance : MulAction ℝ (X ⟿ Y) := MulAction.mk sorry sorry
  instance : DistribMulAction ℝ (X ⟿ Y) := DistribMulAction.mk sorry sorry
  instance : Module ℝ (X ⟿ Y) := Module.mk sorry sorry

  -- IMPORTANT: `X → Y` and `X ⟿ Y` do not have the same topology. 
  -- `X → Y` is just a product topology/initial topology based on all
  -- evaluations for every `x : X`. However `X ⟿ Y` has topology given by point 5 in:
  -- https://en.wikipedia.org/wiki/Convenient_vector_space#Main_properties_of_smooth_calculus
  instance : Vec (X ⟿ Y) := Vec.mk

  -- instance : Coe (X⟿Y) (X→Y) := ⟨λ f => f.1⟩
  instance : CoeFun (X⟿Y) (λ _ => X→Y) := ⟨λ f => f.1⟩


  --- TODO: This should fail fast!!! but it does not :(
  -- set_option synthInstance.maxHeartbeats 5000 in
  -- example {X Y} [Vec X] [Vec Y] (f df : X ⟿ Y) : IsLin (∂ (λ (f : X ⟿ Y) => ∂ f.1) f df) := 
  -- by
  --   infer_instance

  --------------------------------------------------------------------

  @[ext] 
  theorem SmoothMap.ext {X Y} [Vec X] [Vec Y] (f g : X ⟿ Y) : (∀ x, f x = g x) → f = g := sorry


  namespace Smooth

  variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]


  def comp' : (Y ⟿ Z) → (X ⟿ Y) → (X ⟿ Z) := λ f g => ⟨λ x => f (g x), sorry⟩
  def curry' : (X×Y ⟿ Z) → (X ⟿ Y ⟿ Z) := λ f => ⟨λ x => ⟨λ y => f (x,y), sorry⟩, sorry⟩
  def uncurry' : (X ⟿ Y ⟿ Z) → (X×Y ⟿ Z) := λ f => ⟨λ (x,y) => f x y, sorry⟩

  def id : X ⟿ X := ⟨λ x => x, sorry⟩
  def fst : X×Y ⟿ X := ⟨λ (x,y) => x, sorry⟩
  def snd : X×Y ⟿ Y := ⟨λ (x,y) => y, sorry⟩
  def pmap : (X⟿Y) ⟿ (X⟿Z) ⟿ (X⟿Y×Z) := ⟨λ f => ⟨λ g => ⟨λ x => (f x, g x), sorry⟩, sorry⟩, sorry⟩
  def fmap : (X⟿Z) ⟿ (Y⟿W) ⟿ (X×Y⟿Z×W) := ⟨λ f => ⟨λ g => ⟨λ (x,y) => (f x, g y), sorry⟩, sorry⟩, sorry⟩
  def fmap' : (X→Z) ⟿ (Y→W) ⟿ (X×Y→Z×W) := ⟨λ f => ⟨λ g => λ (x,y) => (f x, g y), sorry⟩, sorry⟩
  def pmap' : (X→Y) ⟿ (X→Z) ⟿ (X→Y×Z) := ⟨λ f => ⟨λ g => λ x => (f x, g x), sorry⟩, sorry⟩

  -- Does this one work?
  def comp'' : (Y ⟿ Z) ⟿ (X → Y) ⟿ (X → Z) := ⟨λ f => ⟨λ g => λ x => f (g x), sorry⟩, sorry⟩


  -- (Y⟿Z)×(X→Y) ⟿ (X→Z) 

  def eval : (X⟿Y)×X ⟿ Y := uncurry' id
  def pair : X⟿Y⟿X×Y := curry' id

  @[simp]
  theorem eval_eval (fx : (X⟿Y)×X) : eval fx = fx.1 fx.2 := rfl

  @[simp]
  theorem pair_eval (x : X) (y : Y) : pair x y = (x,y) := rfl
  
  
  def assocl : X×(Y×Z) ⟿ (X×Y)×Z := 
    let F : X×(Y×Z) ⟿ (X×Y)×Z := pmap (pmap fst (comp' fst snd)) (comp' snd snd)     
    ⟨λ (x,(y,z)) => ((x,y),z), 
     by 
       have h : (λ (x,(y,z)) => ((x,y),z)) = F.1 := by simp[pmap, comp', fst, snd]
       rw[h]
       apply F.2⟩

  def assocr : (X×Y)×Z ⟿ X×(Y×Z) := 
    let F : (X×Y)×Z ⟿ X×(Y×Z) := pmap (comp' fst fst) (pmap (comp' snd fst) snd) 
    ⟨λ ((x,y),z) => (x,(y,z)),
     by 
       have h : (λ ((x,y),z) => (x,(y,z))) = F.1 := by simp[pmap, comp', fst, snd]
       rw[h]
       apply F.2⟩

  @[simp]
  theorem assocl_eval (xyz : X×(Y×Z)) : assocl xyz = ((xyz.1,xyz.2.1),xyz.2.2) := rfl

  @[simp]
  theorem assocr_eval (xyz : (X×Y)×Z) : assocr xyz = (xyz.1.1,(xyz.1.2,xyz.2)) := rfl


  def swap : (X×Y) ⟿ (Y×X) := pmap snd fst

  @[simp]
  theorem swap_eval (xy : (X×Y)) : swap xy = (xy.2, xy.1) := rfl

  def rot132 : (X×Y)×Z ⟿ (X×Z)×Y := comp' assocl (comp' (fmap id swap) assocr)

  @[simp]
  theorem rot132_eval (xyz : (X×Y)×Z) : rot132 xyz = ((xyz.1.1, xyz.2), xyz.1.2) := rfl

  def comp : (Y ⟿ Z) ⟿ (X ⟿ Y) ⟿ (X ⟿ Z) := 
    let F₁ : (Y⟿Z)×((X⟿Y)×X) ⟿ Z := comp' eval (fmap id eval)
    curry' (curry' (comp' F₁ assocr))


  @[simp]
  theorem comp_eval (f : Y⟿Z) (g : X ⟿ Y) (x : X) : comp f g x = f (g x) := rfl

  def const : X⟿Y⟿X := curry' fst

  @[simp]
  theorem const_eval (f : Y⟿Z) (g : X ⟿ Y) (x : X) : comp f g x = f (g x) := rfl

  def uncurry : (X ⟿ Y ⟿ Z) ⟿ (X×Y ⟿ Z) := 
    let F : ((X⟿Y⟿Z)×X)×Y ⟿ Z := comp eval (fmap eval id)

    let G₁ : (X×Y ⟿ (X⟿Y⟿Z)×(X×Y)) ⟿ (X×Y ⟿ Z) := comp (comp' F assocl)
    let G₂ : (X⟿Y⟿Z) ⟿ (X×Y ⟿ (X⟿Y⟿Z)×(X×Y)) := pair
    comp' G₁ G₂

  @[simp]
  theorem uncurry_eval (f : X ⟿ Y ⟿ Z) (xy : X×Y) : uncurry f xy = f xy.1 xy.2 := by rfl

  def curry : (X × Y ⟿ Z) ⟿ (X ⟿ Y ⟿ Z) := 

    let G : ((X×Y⟿Z)×Y)×X ⟿ Z := comp (comp (uncurry' id) (fmap id swap)) assocr

    let H : (Y ⟿ (X×Y⟿Z)×Y)×X ⟿ (Y ⟿ ((X×Y⟿Z)×Y)×X) := curry' (comp (fmap eval id) rot132)

    let F₁ : (X×Y⟿Z) ⟿ (Y ⟿ (X×Y⟿Z)×Y) := pair
    let F₂ : (Y ⟿ (X×Y⟿Z)×Y) ⟿ (X ⟿ (Y ⟿ (X×Y⟿Z)×Y)×X) := pair
    let F₃ : (X ⟿ (Y ⟿ (X×Y⟿Z)×Y)×X) ⟿ (X ⟿ (Y ⟿ ((X×Y⟿Z)×Y)×X)) := comp H

    comp (comp (comp G)) (comp F₃ (comp F₂ F₁))

  @[simp]
  theorem curry_eval (f : X×Y ⟿ Z) (x : X) (y : Y) : curry f x y = f (x,y) := by rfl

  def prod : (X → Y ⟿ Z) ⟿ (X→Y) ⟿ (X→Z) := 
    let F : (X → Y ⟿ Z) ⟿ (X→Y) ⟿ (X → Y ⟿ Z)×(X→Y) := pair
    let G₁ : (X → Y ⟿ Z)×(X→Y) ⟿ (X → (Y⟿Z)×Y) := uncurry pmap'
    let G₂ : (X → (Y⟿Z)×Y) ⟿ (X→Z) := comp'' eval
    
    comp (comp (comp G₂ G₁)) F

  @[simp]
  theorem prod_eval (f : X → Y ⟿ Z) : prod f (λ _ => y) x = f x y := by rfl

  def scomb : (X⟿Y⟿Z) ⟿ (X⟿Y) ⟿ X ⟿ Z := 
    let F₁ : (X⟿Y⟿Z)×(X⟿Y)×X ⟿ (X×Y⟿Z)×(X×Y) := fmap uncurry (pmap snd eval)

    comp (curry) (curry (comp eval F₁))


  variable {ι κ : Type} {E F G : ι → Type} {E' : κ → Type} [∀ i, Vec (E i)] [∀ i, Vec (F i)] [∀ i, Vec (G i)] [∀ j, Vec (E' j)]
  instance  [∀ i, Vec (F i)] : Vec ((i : ι) → (F i)) := sorry

  def pmapDep : ((i : ι)→(E i)) ⟿ ((i : ι)→(F i)) ⟿ ((i : ι)→(E i)×(F i)) := ⟨λ f => ⟨λ g => λ x => (f x, g x), sorry⟩, sorry⟩
  def fmapDep : ((i : ι)→(E i)) ⟿ ((j : κ)→(E' j)) ⟿ ((ij : (ι×κ))→(E ij.1)×(E' ij.2)) := ⟨λ f => ⟨λ g => λ (i,j) => (f i, g j), sorry⟩, sorry⟩
  def prodDep : ((i : ι) → E i ⟿ F i) ⟿ ((i : ι) → E i) ⟿ ((i : ι) → F i) := sorry 


  /-- Having jointly smooth evaluation map on a product space, `(X→Y)×X ⟿ Y`, is inconsistent. We can prove that any function is smooth using it.

    This function is famously not continuous on for generic locally convex vector space, in particular (X→ℝ)×X → ℝ (I think that `X` is the dual of the product space `X→ℝ`). Joint continuity would imply that `X→ℝ` is normed vector space.
  -/
  theorem important_issue_with_smooth_maps (ev : (X→Y)×X ⟿ Y) (h : ∀ (f : X→Y) (x : X), ev (f,x) = f x)
    : ∀ (f : X→Y), Mathlib.Convenient.is_smooth f := 
    -- this function can turn any function to a smooth one
    let make_any_smooth := curry' ev
    have is_id : ∀ f, make_any_smooth f = f := by ext; simp[curry',h]; done
    λ f => (is_id f ▸ (make_any_smooth f).2)

  end Smooth

