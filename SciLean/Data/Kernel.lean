structure Kernel where
  byteArray : Type
  byteArraySize : byteArray → Nat
  
  type : Type
  typeDec : DecidableEq type
  void : type
  typeName : type → String

  function : Type
  funDec : DecidableEq function
  funName : function → String
  funArgs : function → Array type
  funOut  : function → type

-- This somehow does not work :(
instance {k : Kernel}  : DecidableEq k.type := k.typeDec
instance {k : Kernel} : DecidableEq k.function := k.funDec

namespace Kernel

  def type.name {k} (t : type k) : String := typeName k t

  instance {k : Kernel} : Inhabited k.type := ⟨k.void⟩

  def function.outType {k} (f : function k) : type k := funOut k f
  def function.nArgs   {k} (f : function k) : Nat := (funArgs k f).size
  def function.argType {k} (f : function k) (i : Nat) : type k := (funArgs k f)[i]

  --- Probably include number of arguments in the type. 
  --- For example define `NArray (t : Type) (n : Nat)` and have `args : NArray (KernelType k) nargs`
  --- We probably also want `let` binding to not redo certain computations.
  inductive Expr (k : Kernel) (args : Array (type k))  where
    | input : (i : Fin args.size) → Expr k args
    | const : type k → (str : String) → Expr k args
    | app : (f : function k) → (fargs : Array (Expr k args)) → Expr k args

  instance {k args} : Inhabited (Expr k args) := ⟨Expr.const k.void ""⟩

  -- Kernel expresion does not have to be well typed, that is why there is Option
  partial def Expr.type {k args} : Expr k args → Option (type k)
    | input i => args[i.1]
    | const t _ => t
    | app f fargs => do
      if f.nArgs != fargs.size then 
        none
      else 
        let mut wellTyped := true
        for i in [0:fargs.size] do
          match fargs[i].type with
            | some t => do
              wellTyped := wellTyped ∧ (f.argType i == t)
            | none => do
              wellTyped := false
        if wellTyped then
          f.outType
        else
          none
  
  def Expr.isWellTyped {k args} (e : Expr k args) : Bool :=
    match e.type with
      | some _ => true
      | none   => false

  class ReflectedType (k : Kernel) (α : Type) extends Inhabited α where
    t : type k
    sizeof : UInt64
    readBytes  : (buffer : byteArray k) → (offset : UInt64) → (h : offset.toNat * sizeof.toNat + sizeof.toNat ≤ byteArraySize k buffer) → α
    writeBytes : (buffer : byteArray k) → (offset : UInt64) → (h : offset.toNat * sizeof.toNat + sizeof.toNat ≤ byteArraySize k buffer) → α → byteArray k
    -- maybe something about compatibility of readBytes and writeBytes like
    --  1. not changing size of byteArray
    --  2. writing changes only designated bytes
    
  def kernelType {k} (α : Type) [ReflectedType k α] : type k := ReflectedType.t α

  class ReflectedFun1 (k : Kernel) {α β} 
        [ReflectedType k α] [ReflectedType k β] 
        (f : α → β) where
   f : function k
   wellTyped : (f.outType = kernelType β) ∧ (f.argType 0 = kernelType α)

  class ReflectedFun2 (k : Kernel) {α0 α1 β} 
        [ReflectedType k α0] [ReflectedType k α1] [ReflectedType k β] 
        (f : α0 → α1 → β) where
    f : function k
    wellTyped : (f.outType = kernelType β) ∧ (f.argType 0 = kernelType α0) ∧ (f.argType 1 = kernelType α1)

  class ReflectedExpr (k args) 
        {α} [ReflectedType k α] 
        (e : α) where  
    expr : Expr k args
    wellTyped : expr.type = some (kernelType α)
  
  -- maybe add style - for now we assume C style syntax
  def expr.generateCode {k args} (e : Expr k args) (name : String) : Option String := 
    match (e.type) with
      | some E => do
        let argsDecl := args.mapIdx (λ i arg => arg.name ++ s!" x{i}") 
                          |> Array.foldl (λ a b => a ++ ", " ++ b) ""
        let mut code := s!"{E.name} {name}({argsDecl})"
        code
      | none => none

  -- instance {α β} (f : α → β) 
  --   [ReflectedType k α] [ReflectedType k β]
  --   [ReflectedFun1 k f]
  --   : ReflectedExpr k args (λ x => f x)
  --   := 
  --   let args := #[ReflectedType.t α]
  --   ⟨Expr.app (ReflectedFun1.f f) #[Expr.input (args := args) ⟨0, sorry⟩]⟩

  -- instance {α β γ} (f : α → β → γ) 
  --   [ReflectedType k α] [ReflectedType k β] [ReflectedType k γ]
  --   [ReflectedFun2 k f]
  --   : ReflectedExprArg2 k (λ x y => f x y)
  --   := sorry
  --   -- ⟨Expr.app (ReflectedFun1.f f) #[Expr.input (args := #[ReflectedType.t α]) ⟨0, sorry⟩]⟩

  -- instance {α β γ} (f : β → γ) (g : α → β) 
  --   [ReflectedType k α] [ReflectedType k β] [ReflectedType k γ]
  --   [ReflectedFun1 k f] [ReflectedExprArg1 k g] 
  --   : ReflectedExprArg1 k (λ x => f (g x))
  --   := ⟨Expr.app (ReflectedFun1.f f) #[ReflectedExprArg1.expr g]⟩

namespace CKernel

  inductive type where
    | void : type
    | core_type (name : String) : type
    | ptr_type : type → type

  def type.typeName : type → String
    | void => "void"
    | core_type name => name
    | ptr_type t => t.typeName ++ "*"

  inductive function where
    | inline_fun (out : type) (args : Array type) (name : String) (body : String)  : function

  def function.funName : function → String
    | inline_fun _ _ name _ => name

  def function.funArgs : function → Array type
    | inline_fun _ args _ _ => args

  def function.funOut : function → type
    | inline_fun out _ _ _ => out

end CKernel


def CKernel : Kernel :=
{
  byteArray := ByteArray
  byteArraySize := ByteArray.size
  
  type := CKernel.type
  typeDec := sorry  -- I think this there is a way to automatically generate this 
  void := CKernel.type.void
  typeName := CKernel.type.typeName

  function := CKernel.function
  funDec := sorry  -- I think this there is a way to automatically generate this 
  funName := CKernel.function.funName
  funArgs := CKernel.function.funArgs
  funOut  := CKernel.function.funOut
}

-- extern this somehow -- as C compiler what is the size of the appropriate element
constant CKernel.type.sizeof (t : CKernel.type) : Nat 

def sizeof (α : Type) [CKernel.ReflectedType α] : Nat := (CKernel.kernelType α).sizeof

variable (t : CKernel.type)

-- Maybe state that buffer.size fits to UInt64
structure CArray (α : Type) [CKernel.ReflectedType α] where
  buffer : CKernel.byteArray
  valid_size : buffer.size % (sizeof α) = 0

instance {α} [CKernel.ReflectedType α] : Inhabited (CArray α) := ⟨ByteArray.empty, sorry⟩ --- 0 % whatever = 0

namespace CArray

  variable {α} [CKernel.ReflectedType α]

  def size (a : CArray α) : Nat := a.buffer.size / (sizeof α)

  def get (a : @& CArray α) (i : @& Fin a.size) : α := ReflectedType.readBytes a.buffer i.1.toUInt64 sorry
  def set (a : CArray α) (i : @& Fin a.size) (val : α) : CArray α := ⟨ReflectedType.writeBytes a.buffer i.1.toUInt64 sorry val, sorry⟩

  constant intro {n} (f : Fin n → α) : CArray α
  constant intro! (f : UInt64 → α) (size : UInt64) : CArray α

  @[simp] axiom intro_size {n} (f : Fin n → α) : (intro f).size = n 
  @[simp] axiom intro!_intro (f : UInt64 → α) (n : UInt64) : intro! f n = intro (λ i : Fin n.toNat => f ⟨i.1, sorry⟩)

end CArray


