import SciLean.Meta.DerivingOp

open Lean Elab Command

namespace SciLean.Meta


private def mkAlgebraInstance (algName : Name) (declName : Name) : TermElabM Unit := do
  let env ← getEnv
  match getStructureInfo? env declName with
  | some info => do
    let structType ← Meta.inferType (mkConst info.structName)
    let instValue ← Meta.forallTelescope structType λ xs _ =>
    do
      let strct ← Meta.mkAppOptM info.structName (xs.map some)
      Meta.mkLambdaFVars xs (← Meta.mkAppM (`SciLean.Meta |>.append algName |>.append `sorryMk) #[strct, (mkConst ``Unit.unit)])

    let instType ← Meta.inferType instValue

    let instName : Name := s!"inst{algName.getString!}{declName.getString!}"
    let instDecl : Declaration := .defnDecl
      {levelParams := [],
       hints := .regular 0,
       safety := .safe,
       type := instType,
       value := instValue,
       name := instName,
       }
    addAndCompile instDecl
    Attribute.add instName "instance" default
  | none =>
    pure default

-- The (_ : Unit) argument is there to only force that all the classes are infered when we apply `mkAppM`
def AddSemigroup.sorryMk (X : Type u) [Add X] (_ : Unit): AddSemigroup X := AddSemigroup.mk sorry
def AddMonoid.sorryMk (X : Type u) [AddSemigroup X] [Zero X] (_ : Unit) : AddMonoid X := AddMonoid.mk sorry_proof sorry_proof nsmulRec sorry_proof sorry_proof

def AddCommMonoid.sorryMk (X : Type u) [AddMonoid X] (_ : Unit) : AddCommMonoid X := AddCommMonoid.mk sorry_proof
def SubNegMonoid.sorryMk (X : Type u) [AddMonoid X] [Neg X] [Sub X] (_ : Unit) : SubNegMonoid X  := SubNegMonoid.mk sorry_proof zsmulRec sorry_proof sorry_proof sorry_proof
def AddGroup.sorryMk (X : Type u) [SubNegMonoid X] (_ : Unit) : AddGroup X      := AddGroup.mk sorry_proof
def AddCommGroup.sorryMk (X : Type u) [AddGroup X] (_ : Unit) : AddCommGroup X  := AddCommGroup.mk sorry_proof

def MulAction.sorryMk (X : Type u) [SMul ℝ X] (_ : Unit) : MulAction ℝ X := MulAction.mk sorry_proof sorry_proof
def DistribMulAction.sorryMk (X : Type u)  [AddMonoid X] [MulAction ℝ X] (_ : Unit) : DistribMulAction ℝ X := DistribMulAction.mk sorry_proof sorry_proof
def Module.sorryMk (X : Type u) [AddCommMonoid X] [DistribMulAction ℝ X] (_ : Unit) : Module ℝ X := Module.mk sorry_proof sorry_proof

def SciLean.Vec.sorryMk (X : Type u) [AddCommGroup X] [Module ℝ X] (_ : Unit) : Vec X := Vec.mk


def mkAddSemigroupHandler (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  if (← declNames.allM (λ name => pure (isStructure env name))) && declNames.size > 0 then
    declNames.forM λ name => do
      liftTermElabM <| mkBinaryOpInstance ``Add ``Add.add name
      liftTermElabM <| mkAlgebraInstance ``AddSemigroup name
    return true
  else
    return false

def mkAddMonoidHandler (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  if (← declNames.allM (λ name => pure (isStructure env name))) && declNames.size > 0 then
    declNames.forM λ name => do
      liftTermElabM <| mkBinaryOpInstance ``Add ``Add.add name
      liftTermElabM <| mkAlgebraInstance ``AddSemigroup name
      liftTermElabM <| mkNullaryOpInstance ``Zero ``Zero.zero name
      liftTermElabM <| mkAlgebraInstance ``AddMonoid name
    return true
  else
    return false

def mkAddCommMonoidHandler (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  if (← declNames.allM (λ name => pure (isStructure env name))) && declNames.size > 0 then
    declNames.forM λ name => do
      liftTermElabM <| mkBinaryOpInstance ``Add ``Add.add name
      liftTermElabM <| mkAlgebraInstance ``AddSemigroup name
      liftTermElabM <| mkNullaryOpInstance ``Zero ``Zero.zero name
      liftTermElabM <| mkAlgebraInstance ``AddMonoid name
      liftTermElabM <| mkAlgebraInstance ``AddCommMonoid name
    return true
  else
    return false

def mkSubNegMonoidHandler (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  if (← declNames.allM (λ name => pure (isStructure env name))) && declNames.size > 0 then
    declNames.forM λ name => do
      liftTermElabM <| mkBinaryOpInstance ``Add ``Add.add name
      liftTermElabM <| mkAlgebraInstance ``AddSemigroup name
      liftTermElabM <| mkNullaryOpInstance ``Zero ``Zero.zero name
      liftTermElabM <| mkAlgebraInstance ``AddMonoid name
      liftTermElabM <| mkAlgebraInstance ``AddCommMonoid name
      liftTermElabM <| mkBinaryOpInstance ``Sub ``Sub.sub name
      liftTermElabM <| mkUnaryOpInstance ``Neg ``Neg.neg name
      liftTermElabM <| mkAlgebraInstance ``SubNegMonoid name
    return true
  else
    return false

def mkAddGroupHandler (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  if (← declNames.allM (λ name => pure (isStructure env name))) && declNames.size > 0 then
    declNames.forM λ name => do
      liftTermElabM <| mkBinaryOpInstance ``Add ``Add.add name
      liftTermElabM <| mkAlgebraInstance ``AddSemigroup name
      liftTermElabM <| mkNullaryOpInstance ``Zero ``Zero.zero name
      liftTermElabM <| mkAlgebraInstance ``AddMonoid name
      liftTermElabM <| mkAlgebraInstance ``AddCommMonoid name
      liftTermElabM <| mkBinaryOpInstance ``Sub ``Sub.sub name
      liftTermElabM <| mkUnaryOpInstance ``Neg ``Neg.neg name
      liftTermElabM <| mkAlgebraInstance ``SubNegMonoid name
      liftTermElabM <| mkAlgebraInstance ``AddGroup name
    return true
  else
    return false

def mkAddCommGroupHandler (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  if (← declNames.allM (λ name => pure (isStructure env name))) && declNames.size > 0 then
    declNames.forM λ name => do
      liftTermElabM <| mkBinaryOpInstance ``Add ``Add.add name
      liftTermElabM <| mkAlgebraInstance ``AddSemigroup name
      liftTermElabM <| mkNullaryOpInstance ``Zero ``Zero.zero name
      liftTermElabM <| mkAlgebraInstance ``AddMonoid name
      liftTermElabM <| mkAlgebraInstance ``AddCommMonoid name
      liftTermElabM <| mkBinaryOpInstance ``Sub ``Sub.sub name
      liftTermElabM <| mkUnaryOpInstance ``Neg ``Neg.neg name
      liftTermElabM <| mkAlgebraInstance ``SubNegMonoid name
      liftTermElabM <| mkAlgebraInstance ``AddGroup name
      liftTermElabM <| mkAlgebraInstance ``AddCommGroup name
    return true
  else
    return false


def mkVecHandler (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  if (← declNames.allM (λ name => pure (isStructure env name))) && declNames.size > 0 then
    declNames.forM λ name => do
      liftTermElabM <| mkBinaryOpInstance ``Add ``Add.add name
      liftTermElabM <| mkAlgebraInstance ``AddSemigroup name
      liftTermElabM <| mkNullaryOpInstance ``Zero ``Zero.zero name
      liftTermElabM <| mkAlgebraInstance ``AddMonoid name
      liftTermElabM <| mkAlgebraInstance ``AddCommMonoid name
      liftTermElabM <| mkBinaryOpInstance ``Sub ``Sub.sub name
      liftTermElabM <| mkUnaryOpInstance ``Neg ``Neg.neg name
      liftTermElabM <| mkAlgebraInstance ``SubNegMonoid name
      liftTermElabM <| mkAlgebraInstance ``AddGroup name
      liftTermElabM <| mkAlgebraInstance ``AddCommGroup name

      liftTermElabM <| mkSMulOpInstance name
      liftTermElabM <| mkAlgebraInstance ``MulAction name
      liftTermElabM <| mkAlgebraInstance ``DistribMulAction name
      liftTermElabM <| mkAlgebraInstance `Module name
      liftTermElabM <| mkAlgebraInstance ``Vec name
    return true
  else
    return false



initialize
  registerDerivingHandler ``AddSemigroup mkAddSemigroupHandler
  registerDerivingHandler ``AddMonoid mkAddMonoidHandler
  registerDerivingHandler ``AddCommMonoid mkAddCommMonoidHandler
  registerDerivingHandler ``SubNegMonoid mkSubNegMonoidHandler
  registerDerivingHandler ``AddGroup mkAddGroupHandler
  registerDerivingHandler ``AddCommGroup mkAddCommGroupHandler
  registerDerivingHandler ``Vec mkVecHandler
