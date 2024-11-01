import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.DiffeologyMap

namespace SciLean


variable
  {X : Type*} {TX : outParam (X → Type*)} [Diffeology X]
  [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
  {Y : Type*} {TY : outParam (Y → Type*)} [Diffeology Y]
  [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY]
  {Z : Type*} {TZ : outParam (Z → Type*)} [Diffeology Z]
  [∀ z, AddCommGroup (TZ z)] [∀ z, Module ℝ (TZ z)] [TangentSpace Z TZ]


variable [Diffeology ℝ] [TangentSpace ℝ (fun _ => ℝ)]
class FiberBundle (TX : (x : X) → Type*) [∀ x, Diffeology (TX x)]
    [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [∀ x, TangentSpace (TX x) (fun _ => (TX x))]
    where
  lift : (c : DiffeologyMap ℝ X) → (s : ℝ) → (v : TX (c s)) → (t : ℝ) → TX (c.1 t)

  lift_inv (c : DiffeologyMap ℝ X) (s : ℝ) (v : TX (c s)) (t : ℝ) :
    lift c t (lift c s v t) s = v

  lift_trans (c : DiffeologyMap ℝ X) (s : ℝ) (v : TX (c s)) (t t' : ℝ) :
    lift c t (lift c s v t) t' = lift c s v t'


class FiberBundle' (E : Type u) (B : Type v)
    [Diffeology E] {TE} [∀ e, AddCommGroup (TE e)] [∀ e, Module ℝ (TE e)] [TangentSpace E TE]
    [Diffeology B] {TB} [∀ b, AddCommGroup (TB b)] [∀ b, Module ℝ (TB b)] [TangentSpace B TB]
    where
  proj : DiffeologyMap E B
  lift (c : DiffeologyMap ℝ B) (s : ℝ) (e : E) (he : proj e = b) : DiffeologyMap ℝ E


variable [Diffeology ℝ] [TangentSpace ℝ (fun _ => ℝ)]
class TangentBundle (TX : (x : X) → Type*) [∀ x, Diffeology (TX x)]
    [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [∀ x, TangentSpace (TX x) (fun _ => (TX x))]
    where
  lift : (c : DiffeologyMap ℝ X) → (s : ℝ) → (v : TX (c s)) → (t : ℝ) → TX (c.1 t)

  lift_inv (c : DiffeologyMap ℝ X) (s : ℝ) (v : TX (c s)) (t : ℝ) :
    lift c t (lift c s v t) s = v

  lift_trans (c : DiffeologyMap ℝ X) (s : ℝ) (v : TX (c s)) (t t' : ℝ) :
    lift c t (lift c s v t) t' = lift c s v t'

  -- lift_shift (c : DiffeologyMap ℝ X) (s : ℝ) (v : TX (c.1 s)) (t h : ℝ) :
  --   lift c s v t = cast (by simp) (lift ⟨fun t => c.1 (t+h), sorry⟩ (s-h) (cast (by simp) v) (t-h))


variable
    [∀ x, Diffeology (TX x)] [∀ x, TangentSpace (TX x) (fun _ => (TX x))] [TangentBundle TX]
    [∀ y, Diffeology (TY y)] [∀ y, TangentSpace (TY y) (fun _ => (TY y))] [TangentBundle TY]


variable
  {E : X → Type*} {TE : (x : X) → E x → Type*} [Diffeology (Sigma E)]
  [∀ x e, AddCommGroup (TE x e)] [∀ x e, Module ℝ (TE x e)] [TangentSpace (Sigma E) (fun p => TX p.1 × TE p.1 p.2)]


def covDeriv (f : (x : X) → E x) (x : X) (dx : TX x) : TE _ (f x)  :=
  let c := TangentSpace.curve x dx
  let c' := fun x => f (c x)
  let c' : DiffeologyMap (Fin 1 → ℝ) (Sigma E) := ⟨fun t => ⟨c t, f (c t)⟩, sorry⟩
  let v'' := TangentSpace.tangent c' sorry (fun _ => 0) (fun _ => 1)
  cast (by simp[c',c]; rw[TangentSpace.curve_at_zero]) v''.2
