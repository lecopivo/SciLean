import Lean
open Lean Elab Command Term Meta

#check synthInstance
#check MetaM

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


@[commandElab check_tc_failure]
def checkTCFailureImpl : CommandElab := fun stx => do
  try 
    let _ ← liftTermElabM (withoutErrToSorry (elabTerm stx[1] none))
    logError "Unexpected success!"
  catch e =>
    logInfo "FAILURE"
    logInfo s!"{← e.toMessageData.toString}"
    logInfo s!"{e.toMessageData.type}"

class C (n : Nat)
instance : C 0 := ⟨⟩
def funC (n : Nat) [C n] := n

-- This behaves as expected
#check_tc_failure funC 0
#check_tc_failure funC 1

class D (n : Nat)
instance {n} [D (n+1)] : D n := ⟨⟩
def funD (n : Nat) [D n] := n

-- I want this to fail as it reaches max heartbeats
#check_tc_failure (funD 0)

class E (n m : Nat)
instance [E n m] [E n (m+1)] : E (n+1) m := ⟨⟩
def funE (n m : Nat) [E n m] := n+m

-- This should fail because we are hitting maxSize 
#check_tc_failure funE 7 0

-- This should succeed as we have searched through everything
set_option synthInstance.maxSize 300 in
#check_tc_failure funE 7 0
