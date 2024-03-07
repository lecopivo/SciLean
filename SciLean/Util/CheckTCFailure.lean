import Lean
open Lean Elab Command Term Meta

#check synthInstance
#check MetaM

/-- Checks if typeclass fails to be synthesized. The failure has to be proper i.e. max hearthbeat is not reached thus all options are exhausted.

TODO: Make more robust! The command currently just checks the error message. Also check for reaching max size. -/
syntax (name := check_tc_failure) "#check_tc_failure" term : command

def Lean.MessageData.type : MessageData → String
  | .ofFormat f => s!"ofFormat: {f}"
  | .ofSyntax s => "ofSyntax"
  | .ofExpr e => s!"ofExpr: {e}"
  | .withContext _ m => s!"withContext {m.type}"
  | .withNamingContext _ m => "namingContext"
  | ofGoal   _ => "goal"
  | nest n m => s!"nest {n}: {m.type}"
  | group g => "group"
  | compose m m' => s!"compose ({m.type}, {m'.type})"
  | tagged n m => "tagged"
  | _ => "unknown"


@[command_elab check_tc_failure]
def checkTCFailureImpl : CommandElab := fun stx => do
  try
    let _ ← liftTermElabM (withoutErrToSorry (elabTerm stx[1] none))
    logError "Unexpected success!"
  catch e =>
    let msg ← e.toMessageData.toString
    let msg' := msg |>.dropWhile (· != '\n') |>.drop 1 |>.dropWhile (· != '\n') |>.drop 1
    if msg'.startsWith "(deterministic) timeout at 'typeclass', maximum number of heartbeats" then
      logError s!"Typeclass synthesis failed by reaching the maximum number of heartbeats!"
    else
      logInfo s!"Proper typeclass failure!\n{msg}"

class C (n : Nat)
instance : C 0 := ⟨⟩
def funC (n : Nat) [C n] := n

-- This behaves as expected
-- #check_tc_failure funC 0 -- fails as expected
#check_tc_failure funC 1

class D (n : Nat)
instance {n} [D n] : D (n+1) := ⟨⟩
def funD (n : Nat) [D n] := n

-- I want this to fail as it reaches max heartbeats
#check_tc_failure (funD 100)

-- set_option synthInstance.maxHeartbeats 50 in
-- #check_tc_failure (funD 100) -- correctly fails because reaching max hearthbeat

set_option synthInstance.maxSize 1000 in
#check_tc_failure (funD 100)
