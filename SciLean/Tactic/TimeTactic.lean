import Lean
import Aesop

open Lean Meta Elab Term Tactic Conv in
elab "time_tactic" t:conv : conv => do

  let target ← getMainTarget
  let ((targetNew, proof),time) ← Aesop.time <| convert target (withTacticInfoContext (← getRef) (evalTactic t))
  liftMetaTactic1 fun mvarId => mvarId.replaceTargetEq targetNew proof

  log s!"tactic {t.raw.prettyPrint} took {time.printAsMillis}" .information
