import SciLean.Core.Functions

namespace SciLean


class VecMonad (m : Type u → Type v) extends Monad m, LawfulMonad m where
  vecM (X) [Vec X] : Vec (m X)
  pureZero {X} : X → m X
  add_pureZero_right {X} [Vec X] (mx : m X) (y : X) : mx + pureZero y = bind mx (λ x => pure (x + y))
  bind_pureZero_pure {X Y} (x : X) (f : X → Y) : bind (pureZero x) (λ x => pure (f x)) = pureZero (f x)

export VecMonad (pureZero)

namespace VecMonad

  attribute [simp] add_pureZero_right bind_pureZero_pure
  attribute [reducible] vecM

  @[reducible]
  instance {m X} [inst : VecMonad m] [Vec X] : Vec (m X) := inst.vecM X

  @[simp]
  theorem add_pureZero_left {X} [Vec X] [VecMonad m] (mx : m X) (y : X) 
    : pureZero y + mx = bind mx (λ x => pure (y + x)) := by rw[add_comm]; simp; simp only [add_comm]; done

  @[simp]
  theorem add_pure_pureZero {m} [VecMonad m] {X} [Vec X] (x y : X)
    : (pure x : m X) + pureZero y = pure (x + y) := by simp; done

  @[simp]
  theorem add_pureZero_pure {m} [VecMonad m] {X} [Vec X] (x y : X)
    : (pureZero x : m X) + pure y = pure (x + y) := by rw[add_comm]; simp; rw[add_comm]; done

  @[simp]
  theorem add_pureZero_pureZero {m} [VecMonad m] {X} [Vec X] (x y : X)
    : (pureZero x : m X) + pureZero y = pureZero (x + y) := by simp; done

  -- @[simp]
  -- theorem bind_pureZero_pure {m} [VecMonad m] {X} [Vec X] (x : X) (f : X → Y)
  --   : bind (pureZero x) (λ x => pure (f x)) = pureZero (f x) := by simp; done


section VectorMonads

@[reducible]
instance Id.instVecMonad : VecMonad Id where
  vecM := λ X inst => inst
  pureZero := id
  add_pureZero_right := by simp
  bind_pureZero_pure := by simp

-- set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.simp.unify true in
@[reducible]
instance StateT.instVecMonad [Vec σ] [VecMonad m] : VecMonad (StateT σ m) where
  vecM := λ X inst => by simp[StateT]; infer_instance
  pureZero := λ x s => pureZero (x, (0:σ))
  add_pureZero_right := by 
    intro X inst mx y; funext s
    simp[pure, StateT.pure, bind, StateT.bind] 
    rw[fun_add_eval]; simp [prod_add_elemwise]
    done
  bind_pureZero_pure := by
    intro X inst mx y; funext s
    simp[pure, StateT.pure, bind, StateT.bind]
    done

