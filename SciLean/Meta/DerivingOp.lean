import SciLean.Core.Objects.Vec
import Lean.Elab.Deriving.Basic

open Lean Elab Command

namespace SciLean.Meta


def mkBinaryOpInstance (className opName : Name) (declName : Name) : TermElabM Unit := do
  let env ← getEnv
  match getStructureInfo? env declName with
  | some info => do
    let structType ← Meta.inferType (mkConst info.structName)
    let instValue ← Meta.forallTelescope structType λ xs _ =>
    do
      let strct ← Meta.mkAppOptM info.structName (xs.map some)
      let binOp ← Meta.withLocalDecl `x default strct λ x =>
                   Meta.withLocalDecl `y default strct λ y => do
        let mut fields := #[]
        for i in [0:info.fieldNames.size] do
          fields := fields.push (← Meta.mkAppM opName #[x.proj info.structName i, y.proj info.structName i])
        (Meta.mkLambdaFVars #[x,y] (← Meta.mkAppM (info.structName.append `mk) fields))

      Meta.mkLambdaFVars xs (← Meta.mkAppM (className.append `mk) #[binOp])

    let instType ← Meta.inferType instValue

    let instName : Name := declName.append `instances |>.append className
    let instDecl : Declaration := .defnDecl
      {levelParams := [],
       hints := .regular 0,
       safety := .safe,
       type := instType,
       value := instValue,
       name := instName,
       }
    addAndCompile instDecl
    Attribute.add instName `instance default
  | none =>
    pure default

def mkBinaryOpHandler (className opName : Name) (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  if (← declNames.allM (λ name => pure (isStructure env name))) && declNames.size > 0 then
    declNames.forM λ name => do
      liftTermElabM <| mkBinaryOpInstance className opName name
    return true
  else
    return false

def mkUnaryOpInstance (className opName : Name) (declName : Name) : TermElabM Unit := do
  let env ← getEnv
  match getStructureInfo? env declName with
  | some info => do
    let structType ← Meta.inferType (mkConst info.structName)
    let instValue ← Meta.forallTelescope structType λ xs _ =>
    do
      let strct ← Meta.mkAppOptM info.structName (xs.map some)
      let op ← Meta.withLocalDecl `x default strct λ x => do
        let mut fields := #[]
        for i in [0:info.fieldNames.size] do
          fields := fields.push (← Meta.mkAppM opName #[x.proj info.structName i])
        (Meta.mkLambdaFVars #[x] (← Meta.mkAppM (info.structName.append `mk) fields))

      Meta.mkLambdaFVars xs (← Meta.mkAppM (className.append `mk) #[op])

    let instType ← Meta.inferType instValue

    let instName : Name := declName.append `instances |>.append className
    let instDecl : Declaration := .defnDecl
      {levelParams := [],
       hints := .regular 0,
       safety := .safe,
       type := instType,
       value := instValue,
       name := instName,
       }
    addAndCompile instDecl
    Attribute.add instName `instance default
  | none =>
    pure default

def mkUnaryOpHandler (className opName : Name) (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  if (← declNames.allM (λ name => pure (isStructure env name))) && declNames.size > 0 then
    declNames.forM λ name => do
      liftTermElabM <| mkUnaryOpInstance className opName name
    return true
  else
    return false

def mkNullaryOpInstance (className opName : Name) (declName : Name) : TermElabM Unit := do
  let env ← getEnv
  match getStructureInfo? env declName with
  | some info => do
    let structType ← Meta.inferType (mkConst info.structName)
    let instValue ← Meta.forallTelescope structType λ xs _ => do
      let strct ← Meta.mkAppOptM info.structName (xs.map some)
      let op ← Meta.withLocalDecl `x default strct λ x => do
        let mut fields := #[]
        for i in [0:info.fieldNames.size] do
          fields := fields.push (← Meta.mkAppOptM opName #[← Meta.inferType (x.proj info.structName i),none])
        Meta.mkAppM (info.structName.append `mk) fields

      Meta.mkLambdaFVars xs (← Meta.mkAppM (className.append `mk) #[op])

    let instType ← Meta.inferType instValue

    let instName : Name := declName.append `instances |>.append className
    let instDecl : Declaration := .defnDecl
      {levelParams := [],
       hints := .regular 0,
       safety := .safe,
       type := instType,
       value := instValue,
       name := instName,
       }
    addAndCompile instDecl
    Attribute.add instName `instance default
  | none =>
    pure default

def mkNullaryOpHandler (className opName : Name) (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  if (← declNames.allM (λ name => pure (isStructure env name))) && declNames.size > 0 then
    declNames.forM λ name => do
      liftTermElabM <| mkNullaryOpInstance className opName name
    return true
  else
    return false

def mkSMulOpInstance (declName : Name) : TermElabM Unit := do
  let env ← getEnv
  match getStructureInfo? env declName with
  | some info => do
    let structType ← Meta.inferType (mkConst info.structName)
    let instValue ← Meta.forallTelescope structType λ xs _ =>
    do
      let strct ← Meta.mkAppOptM info.structName (xs.map some)
      let binOp ← Meta.withLocalDecl `s default (mkConst `Real) λ s =>
                   Meta.withLocalDecl `x default strct λ x => do
        let mut fields := #[]
        for i in [0:info.fieldNames.size] do
          fields := fields.push (← Meta.mkAppM ``SMul.smul #[s, x.proj info.structName i])
        (Meta.mkLambdaFVars #[s,x] (← Meta.mkAppM (info.structName.append `mk) fields))

      Meta.mkLambdaFVars xs (← Meta.mkAppM ``SMul.mk #[binOp])

    let instType ← Meta.inferType instValue

    let instName : Name := declName.append `instances |>.append `SMul
    let instDecl : Declaration := .defnDecl
      {levelParams := [],
       hints := .regular 0,
       safety := .safe,
       type := instType,
       value := instValue,
       name := instName}
    addAndCompile instDecl
    Attribute.add instName `instance default
  | none =>
    pure default


def mkSMulOpHandler (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  if (← declNames.allM (λ name => pure (isStructure env name))) && declNames.size > 0 then
    declNames.forM λ name => do
      liftTermElabM <| mkSMulOpInstance name
    return true
  else
    return false

initialize
  registerDerivingHandler ``Add (mkBinaryOpHandler ``Add ``Add.add)
  registerDerivingHandler ``Mul (mkBinaryOpHandler ``Mul ``Mul.mul)
  registerDerivingHandler ``Sub (mkBinaryOpHandler ``Sub ``Sub.sub)
  registerDerivingHandler ``Div (mkBinaryOpHandler ``Div ``Div.div)
  registerDerivingHandler ``Neg (mkUnaryOpHandler ``Neg ``Neg.neg)
  registerDerivingHandler ``Zero (mkNullaryOpHandler ``Zero ``Zero.zero)
  registerDerivingHandler ``One  (mkNullaryOpHandler ``One ``One.one)
  registerDerivingHandler ``SMul mkSMulOpHandler
