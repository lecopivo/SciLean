import SciLean.Core.Attributes
import SciLean.Core.Defs
import SciLean.Core.Meta.FunctionProperty
import SciLean.Core.Meta.RewriteBy

import SciLean.Tactic.AutoDiff

import SciLean.Data.ArraySet

namespace SciLean

--------------------------------------------------------------------------------
-- isSmooth
--------------------------------------------------------------------------------

@[inline]
def _root_.Array.partitionM {m} [Monad m] (p : α → m Bool) (as : Array α) : m (Array α × Array α × Array (Sum Nat Nat)) := do
  let mut bs := #[]
  let mut cs := #[]
  let mut ids : Array (Sum Nat Nat) := #[]
  let mut i := 0
  let mut j := 0
  for a in as do
    if ← p a then
      bs := bs.push a
      ids := ids.push (.inl i)
      i := i + 1
    else
      cs := cs.push a
      ids := ids.push (.inr j)
      j := j + 1
  return (bs, cs, ids)

def _root_.Array.merge (ids : Array (Sum Nat Nat)) (bs cs : Array α) [Inhabited α] : Array α :=
  ids.map λ id => 
    match id with
    | .inl i => bs[i]!
    | .inr j => cs[j]!

theorem isLin_isSmooth {X Y} [Vec X] [Vec Y] {f : X → Y} [inst : IsLin f] : IsSmooth f := inst.isSmooth

syntax "isSmooth" bracketedBinder* (":=" term)? : argProp

open Lean Parser.Term Lean.Elab Meta

#check Command.liftCoreM
#check TermElabM

set_option linter.unusedVariables false 

#check TheoremVal.mk

elab_rules : command
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec isSmooth $extraAssumptions:bracketedBinder* $[:= $proof:term]?) => do

  let data ← Command.liftTermElabM <| liftMacroM <| FunctionPropertyData.parse id parms retType arg

  let mainArgNames := data.mainArgIds.map (λ i => data.argName! i)

  Command.liftTermElabM  do
    let funStx ← liftMacroM do
      let data ← FunctionPropertyData.parse id parms retType arg
      let funBinders ← data.binders.mapM (λ b => b.toFunBinder)
      let args := data.binders.filterMap (λ b => if b.isExplicit then some b.getIdent else none)
      dbg_trace  s!"args: {args.map λ arg => arg.raw.prettyPrint}"

      `(λ $funBinders* => $id $args*)

    IO.println s!"funStx {funStx.raw.prettyPrint}"
    let function ← Term.elabTerm funStx none

    IO.println s!"Function {← ppExpr function} : {← ppExpr (← inferType function)}"
  
    Term.elabBinders parms λ xs => do
      IO.println s!"Elaborated binders: {← xs.mapM λ x => do pure s!"{← x.fvarId!.getUserName} {repr (← x.fvarId!.getBinderInfo)} {← ppExpr (← x.fvarId!.getType)}" }"

    lambdaTelescope function λ xs b => do

      let xName := `x

      let ys ← xs.filterM (λ x => do  if (←x.fvarId!.getUserName)==xName then return false else return true)
      let x ← xs.filterM (λ x => do  if (←x.fvarId!.getUserName)==xName then return true else return false)
      
      let f' ← mkLambdaFVars ys (← mkAppM ``IsSmooth #[← mkLambdaFVars x b])
      IO.println s!"smoothness in x: {← ppExpr f'}"


    lambdaTelescope function λ xs b => do

      let xName := `x

      let ys ← xs.filterM (λ x => do  if (←x.fvarId!.getUserName)==xName then return false else return true)
      let x ← xs.filterM (λ x => do  if (←x.fvarId!.getUserName)==xName then return true else return false)

      let f' ← mkLambdaFVars ys (← mkAppM ``IsSmooth #[← mkLambdaFVars x b])
      IO.println s!"smoothness in x: {← ppExpr f'}"


    let smoothness ← 
    withLocalDecl `T .implicit (mkSort levelOne)               λ T => do
      withLocalDecl "inst✝" .instImplicit (← mkAppM ``Vec #[T]) λ TVec => do
        withLocalDecl `t .default T                                λ t => do
          lambdaTelescope function λ xs b => do

            let mainArgTest := λ arg : Expr => do 
              let name ← arg.fvarId!.getUserName
              if (mainArgNames.find? (λ name' => name' == name)).isSome then -- 
                return true
              else 
                return false

            let (mainArgs, contextArgs, ids) ← xs.partitionM mainArgTest

            -- IO.println s!"main args: {← mainArgs.mapM (λ arg => ppExpr arg)}"

            let mainArgsDecls ← mainArgs.mapM λ arg => do
              let name ← arg.fvarId!.getUserName
              let bi := BinderInfo.default
              let type ← mkArrow T (← inferType arg)
              pure (name, bi, λ (_:Array Expr) => (pure type : TermElabM Expr))

            withLocalDecls mainArgsDecls λ xs => do

              let isSmoothDecls ← xs.mapM (λ x => do
                let name : Name := "inst✝"
                let bi := BinderInfo.instImplicit
                let type ← mkAppM ``IsSmooth #[x]
                return (name, bi, λ (_:Array Expr) => (pure type : TermElabM Expr)))

              withLocalDecls isSmoothDecls λ smoothArgs => do
                let xts ← xs.mapM (λ xt => mkAppM' xt #[t])
                let replacePairs := mainArgs.zip xts
                let b' := replacePairs.foldl (init := b)
                            λ b (x,xt) => b.replace (λ x' => if x==x' then some xt else none)
                let f ← liftMetaM <|
                  (mkLambdaFVars #[t] b' 
                  >>= λ x => mkAppM ``IsSmooth #[x] 
                  >>= mkForallFVars smoothArgs
                  >>= mkForallFVars (ids.merge xs contextArgs)
                  >>= mkForallFVars #[T,TVec])

                IO.println s!"smoothness in x and y: {← ppExpr f}"
                pure f


    -- get rid of some universe metavariables
    let smoothness ← instantiateMVars smoothness
    let prf ← 
      forallTelescope smoothness λ xs b => do
        let val ← Term.elabTermAndSynthesize proof.get! b 
        mkLambdaFVars xs val


    let info : TheoremVal :=
    {
      name := id.getId.append ((`arg_).appendAfter data.mainArgString) |>.append `isSmooth
      type := smoothness
      value := prf
      levelParams := []
    }

    addDecl (.thmDecl info)
    addInstance info.name .local 1000
  
  IO.println "hihi"


-- For a give function/constant property and arguments this gives you the name of the theorem talking about the property in those arguments
-- extraPreArgNum and extraPostArgNum tells you the number of additional arguments compared to the arguments of the function/constant
structure FunctionTheorem where
  thrm : Name
  extraPreArgNum : Nat
  extraPostArgNum : Nat

-- Retrieve theorem for a give function/constant, function transform/property and set of arguments indices 
-- For example `HAdd.hAdd` has 6 arguments `{X Y Z} [HAdd X Y Z] x y`
-- and it has differential, IsSmooth in [4,5] and [4] and [5]
-- but is IsLin, adjoint only in [4,5]
def FunctionTheorems : PersistentHashMap (Name × Name) (PersistentHashMap (ArraySet Nat) FunctionTheorem) := sorry


def getFunctionTheorem (constName : Name) (transOrPropName : Name) (fvar : FVarId) (args : Array Expr) : Option Expr := sorry

-- set_option pp.funBinderTypes true in
function_properties HAdd.hAdd {X : Type} [Vec X]  (x y : X) : X
argument (x,y)
  isSmooth := by admit
argument x
  isSmooth := by admit
argument y
  isSmooth := by admit


#check HAdd.hAdd.arg_xy.isSmooth
#check HAdd.hAdd.arg_x.isSmooth
#check HAdd.hAdd.arg_y.isSmooth


instance {X} [Vec X] : IsSmooth (λ x : X => x) := sorry
instance {X Y} [Vec X] [Vec Y] (x : X): IsSmooth (λ y : Y => x) := sorry

example : IsSmooth λ x : ℝ => x + x := by infer_instance

example (y : ℝ) : IsSmooth λ x : ℝ => x + y := by infer_instance

set_option trace.Meta.synthInstance true in
example (y : ℝ) : IsSmooth λ x : ℝ => y + x := by apply HAdd.hAdd.arg_y.isSmooth



  -- let instanceId := mkIdent $ data.funPropNamespace.append "isSmooth"

  -- let (instanceType, extraBinders) ← 
  --   match data.mainArgNum with 
  --   | 0 => Macro.throwError "Must specify at least one argument!" 
  --   | 1 => pure (← `(IsSmooth  $(← data.mkLambda)), (#[] : Array BracketedBinder))
  --   | _ => do 
  --     let (T, mainBinders, lambda) ← data.mkCompositionLambda
  --     let TBinders : Array BracketedBinder :=  #[← `(bracketedBinderF| {$T : Type _}), ← `(bracketedBinderF| [Vec $T])]
  --     let mainAssumptions ← mainBinders.mapM (β := BracketedBinder) (λ b => `(bracketedBinderF| [IsSmooth $b.getIdent] ))
  --     let instType ← `(IsSmooth $lambda)
  --     pure (instType, TBinders.append (mainBinders.append mainAssumptions))

  -- let proof ← 
  --   match proof with
  --   | none => `(term| by first | apply isLin_isSmooth | infer_instance | (unfold $id; infer_instance); done)
  --   | some prf =>pure  prf

  -- let finalCommand ←
  --     `(@[fun_prop] theorem $instanceId $data.contextBinders* $extraBinders* $extraAssumptions* : $instanceType := $proof)
  
  -- return finalCommand 


