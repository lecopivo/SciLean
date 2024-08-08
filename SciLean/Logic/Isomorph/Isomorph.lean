import SciLean.Logic.Isomorph.IsomorphicType

open Lean

namespace SciLean

variable
  {α β γ : Type _}
  {α' β' γ' : outParam (Type _)}
  (tag : Name)
  [IsomorphicType tag α α']
  [IsomorphicType tag β β']
  [IsomorphicType tag γ γ']

namespace isomorph


@[fun_trans]
theorem id_rule :
    isomorph tag (fun (x : α) => x)
    =
    fun (x : α') => x := by
  funext _; simp[isomorph]


@[fun_trans]
theorem const_rule (y : β) :
    isomorph tag (fun (_ : α) => y)
    =
    fun (_ : α') => (IsomorphicType.equiv tag) y := by
  funext _; simp[isomorph]

@[fun_trans]
theorem comp_rule (f : β → γ) (g : α → β) :
    isomorph tag (fun x => f (g x))
    =
    fun x => isomorph tag f (isomorph tag g x) := by
  funext _; unfold isomorph; simp

@[fun_trans]
theorem let_rule (f : α → β → γ) (g : α → β) :
    isomorph tag (fun x => let y := g x; f x y)
    =
    fun x' =>
      let y' := isomorph tag g x'
      isomorph tag (fun (xy : α×β) => f xy.1 xy.2) (x', y') := by
  funext x'; simp[isomorph, IsomorphicType.equiv, -isomorph.app]

@[fun_trans]
theorem apply_rule (x : α) :
    isomorph tag (fun (f : α → β) => f x)
    =
    fun (f : α' → β') => f ((IsomorphicType.equiv tag) x) := by
  funext _; simp[isomorph, invIsomorph, IsomorphicType.equiv]

@[fun_trans]
theorem pi_rule (f : α → β → γ) :
    isomorph tag (fun x y => f x y)
    =
    fun x' => isomorph tag (f ((IsomorphicType.equiv tag).symm x')) := by
  funext x'; simp[isomorph, IsomorphicType.equiv]



----------------------------------------------------------------------------------------------------


@[fun_trans]
theorem _root_.Prod.mk.isomorph_rule (f : α → β) (g : α → γ) :
    isomorph tag (fun x => (f x, g x))
    =
    fun x' =>
      let y' := isomorph tag f x'
      let z' := isomorph tag g x'
      (y', z')  := by rfl

@[fun_trans]
theorem _root_.Prod.fst.isomorph_rule (f : α → β×γ) :
    isomorph tag (fun x => (f x).1)
    =
    fun x =>
      let f' := isomorph tag f
      (f' x).1  := by rfl

@[fun_trans]
theorem _root_.Prod.snd.isomorph_rule (f : α → β×γ) :
    isomorph tag (fun x => (f x).1)
    =
    fun x =>
      let f' := isomorph tag f
      (f' x).1  := by rfl
