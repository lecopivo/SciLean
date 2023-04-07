import SciLean.Core.Meta.FunctionProperty.Syntax

namespace SciLean

instance {X} [Vec X] : IsSmooth (λ x : X => x) := sorry
instance {X Y} [Vec X] [Vec Y] (x : X): IsSmooth (λ y : Y => x) := sorry
instance {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] : IsSmooth (λ x  => f (g x)) := sorry
instance {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y) (g : X → Z) [IsSmooth f] [IsSmooth g] : IsSmooth (λ x  => (f x, g x)) := sorry

instance {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] (f : Y → Z) (g : X → Y) [HasAdjoint f] [HasAdjoint g] : HasAdjoint (λ x  => f (g x)) := sorry
instance {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] (f : X → Y) (g : X → Z) [HasAdjoint f] [HasAdjoint g] : HasAdjoint (λ x  => (f x, g x)) := sorry


instance {X Y} [Vec X] [Vec Y] (x : X): IsSmooth (λ xy : X×Y => xy.1) := sorry
instance {X Y} [Vec X] [Vec Y] (x : X): IsSmooth (λ xy : X×Y => xy.2) := sorry

@[simp]
theorem diff_id {X} [Vec X] 
  : ∂ (λ x : X => x) 
    =
    λ x dx => dx := sorry

@[simp]
theorem diff_const {X} [Vec X] (x : X)
  : ∂ (λ y : Y => x) 
    =
    λ y dy => 0 := sorry

@[simp]
theorem diff_comp {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g]
  : ∂ (λ x => f (g x)) 
    =
    λ x dx => ∂ f (g x) (∂ g x dx) := sorry

@[simp]
theorem tangentMap_comp {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g]
  : 𝒯 (λ x => f (g x)) 
    =
    λ x dx => 
      let (y,dy) := 𝒯 g x dx 
      𝒯 f y dy 
  := sorry

@[simp]
theorem adjoint_comp {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] (f : Y → Z) (g : X → Y) [HasAdjoint f] [HasAdjoint g]
  : (λ x => f (g x))†
    =
    λ z => g† (f† z)
  := sorry


@[simp]
theorem diff_prodMk {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y) (g : X → Z) [IsSmooth f] [IsSmooth g]
  : ∂ (λ x => (f x, g x)) 
    =
    λ x dx => (∂ f x dx, ∂ g x dx) := sorry

@[simp]
theorem tangentMap_prodMk {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y) (g : X → Z) [IsSmooth f] [IsSmooth g]
  : 𝒯 (λ x => (f x, g x)) 
    =
    λ x dx => 
      let (y,dy) := 𝒯 f x dx
      let (z,dz) := 𝒯 g x dx
      ((y,z), (dy,dz)) := sorry

@[simp]
theorem adjoint_prodMk {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] (f : X → Y) (g : X → Z) [HasAdjoint f] [HasAdjoint g]
  : (λ x => (f x, g x))†
    =
    λ (y,z) => 
      f† y + g† z := sorry


instance {X} [SemiHilbert X] : HasAdjDiff (λ x : X => x) := sorry
instance {X Y} [SemiHilbert X] [SemiHilbert Y] (x : X): HasAdjDiff (λ y : Y => x) := sorry

theorem isLin_isSmooth {X Y} [Vec X] [Vec Y] {f : X → Y} [inst : IsLin f] : IsSmooth f := inst.isSmooth
theorem hasAdjoint_on_FinVec {X Y ι κ} {_ : Enumtype ι} {_ : Enumtype κ} [FinVec X ι] [FinVec Y κ] {f : X → Y} [inst : IsLin f] : HasAdjoint f := sorry
theorem hasAdjDiff_on_FinVec {X Y ι κ} {_ : Enumtype ι} {_ : Enumtype κ} [FinVec X ι] [FinVec Y κ] {f : X → Y} [inst : IsSmooth f] : HasAdjDiff f := sorry



function_properties HAdd.hAdd {X : Type} (x y : X) : X
argument (x,y) [Vec X]
  IsLin    := sorry,
  IsSmooth := by apply isLin_isSmooth,
  funTrans SciLean.differential := λ dx dy => dx + dy by sorry 
  by
    simp only
      [diff_comp (λ xy : X×X => xy.fst + xy.snd) (λ t => (x t, y t)),
       HAdd.hAdd.arg_a4a5.differential_simp,
       diff_prodMk]
    done,
  funTrans SciLean.tangentMap := λ dx dy => (x + y, dx + dy)  by sorry 
  by 
    simp [tangentMap_comp (λ xy : X×X => xy.fst + xy.snd) (λ t => (x t, y t))]
    simp [HAdd.hAdd.arg_a4a5.tangentMap_simp]
    done
argument (x,y) [SemiHilbert X]
  HasAdjoint := sorry,
  HasAdjDiff := sorry,
  funTrans SciLean.adjoint := λ xy' => (xy', xy')  by sorry 
  by 
    simp [adjoint_comp (λ xy : X×X => xy.fst + xy.snd) (λ t => (x t, y t))]
    simp [HAdd.hAdd.arg_a4a5.adjoint_simp]
    done,
  funTrans SciLean.adjointDifferential := λ xy' => (xy', xy')  by sorry by sorry
argument x
  IsSmooth [Vec X] := by infer_instance,
  HasAdjDiff [SemiHilbert X] := by infer_instance,
  funTrans SciLean.differential [Vec X] := λ dx => dx by
    simp [HAdd.hAdd.arg_a4a5.differential_simp']
    done
  by
    sorry,
  funTrans SciLean.tangentMap [Vec X] := λ dx => (x+y, dx) by 
    simp [HAdd.hAdd.arg_a4a5.differential_simp', tangentMap]
    done
  by
    sorry
argument y
  IsSmooth [Vec X] := by apply HAdd.hAdd.arg_a4a5.IsSmooth',
  HasAdjDiff [SemiHilbert X] := by apply HAdd.hAdd.arg_a4a5.HasAdjDiff',
  funTrans SciLean.differential [Vec X] := λ dy => dy by 
    rw [HAdd.hAdd.arg_a4a5.differential_simp']; simp
    done
  by
    sorry


def foo {α β γ : Type} (a : α) (b : β) (c : γ) : γ := sorry

function_properties SciLean.foo {α β γ : Type} (a : α) (b : β) (c : γ)
argument (a,c) [Vec α] [Vec γ]
  IsLin := sorry,
  IsSmooth := isLin_isSmooth,
  funTrans SciLean.differential := sorry by sorry by sorry,
  funTrans SciLean.tangentMap := sorry by sorry by sorry
argument (a,c) [SemiHilbert α] [SemiHilbert γ]
  HasAdjoint := sorry,
  HasAdjDiff := sorry,
  funTrans SciLean.adjoint := sorry  by sorry by sorry,
  funTrans SciLean.adjointDifferential := sorry  by sorry by sorry,
  funTrans SciLean.reverseDifferential := sorry  by sorry by sorry
argument (a,b,c) [SemiHilbert α] [SemiHilbert β] [SemiHilbert γ]
  HasAdjoint := sorry,
  HasAdjDiff := sorry,
  funTrans SciLean.adjoint := λ c => (0,0,c) by sorry 
  by 
    simp only 
         [adjoint_comp (λ abc : α×β×γ => foo abc.1 abc.2.1 abc.2.2) (λ t => (a t, b t, c t)),
          adjoint_prodMk,
          foo.arg_abc.adjoint_simp,
          add_assoc]
    done,
  funTrans SciLean.adjointDifferential := sorry  by sorry by sorry,
  funTrans SciLean.reverseDifferential := sorry  by sorry by sorry


#check foo.arg_ac.adjoint
#check foo.arg_ac.adjointDifferential


#eval printFunctionTheorems
