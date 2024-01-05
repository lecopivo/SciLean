import SciLean.Core.Objects.FinVec
import SciLean.Lean.Meta.Basic
import SciLean.Data.Index

open Lean Meta Qq

namespace SciLean

variable {α : Type _} 
variable [MonadControlT MetaM n] [Monad n]


private partial def withEnumTypeImpl
  (I : Expr) (v w : Level) (k : Array Expr → MetaM α) : MetaM α := do
  loop I #[] k
where
  loop (I : Expr) (acc : Array Expr) (k : Array Expr → MetaM α) : MetaM α := do
    let .some ⟨u,_⟩ ← isTypeQ I | throwError "invalid type {← ppExpr I}"
    let cls := (Expr.const ``EnumType [u,v,w]).app I
    match ← synthInstance? cls with
    | .some _ => k acc
    | none => 
      match I with
      | .app .. => 
        if (I.isAppOfArity' ``Prod 2) ||
           (I.isAppOfArity' ``ColProd 2) ||
           (I.isAppOfArity' ``Sum 2) then
          let X₁ := I.getArg! 0
          let X₂ := I.getArg! 1
          loop X₁ acc (fun acc' => loop X₂ acc' k)
        else
          throwError "dont' know how to extend context to have instance `{← ppExpr cls}`"
      | .fvar _ => 
        withLocalDecl (← mkAuxName `inst 0) .instImplicit cls fun inst => 
          k (acc.push inst)
      | _ => 
        throwError "dont' know how to extend context to have instance `{← ppExpr cls}`"

/-- Modifies the local context such that `I` has instance `EnumType I`

All newly introduced free variables are passed to k. 

If necessary it introduces
- `EnumType J` if `J` is fvar
-/
private partial def withEnumType
  (I : Expr) (v w : Level) (k : Array Expr → n α) : n α := do
  map1MetaM (fun k => withEnumTypeImpl I v w k) k



private partial def withIndexImpl 
  (I : Expr) (v w : Level) (k : Array Expr → MetaM α) : MetaM α := do
  loop I #[] k
where
  loop (I : Expr) (acc : Array Expr) (k : Array Expr → MetaM α) : MetaM α := do
    let .some ⟨u,_⟩ ← isTypeQ I | throwError "invalid type {← ppExpr I}"
    let cls := (Expr.const ``Index [u,v,w]).app I
    match ← synthInstance? cls with
    | .some _ => k acc
    | none => 
      match I with
      | .app .. => 
        if (I.isAppOfArity' ``Prod 2) ||
           (I.isAppOfArity' ``ColProd 2) ||
           (I.isAppOfArity' ``Sum 2) then
          let X₁ := I.getArg! 0
          let X₂ := I.getArg! 1
          loop X₁ acc (fun acc' => loop X₂ acc' k)
        else
          throwError "dont' know how to extend context to have instance `{← ppExpr cls}`"
      | .fvar _ => 
        withLocalDecl (← mkAuxName `inst 0) .instImplicit cls fun inst => 
          k (acc.push inst)
      | _ => 
        throwError "dont' know how to extend context to have instance `{← ppExpr cls}`"


/-- Modifies the local context such that `I` has instance `Index I`

All newly introduced free variables are passed to k. 

If necessary it introduces
- `Index J` if `J` is fvar

It modifies existing instances 
- `EnumType J` to `Index J`
-/
def withIndex (I : Expr) (v w : Level) (k : Array Expr → n α) : n α := do
  map1MetaM (fun k => withIndexImpl I v w k) k



/-- Modifies the local context such that `X` has instance `Vec K X`

All newly introduced free variables are passed to k. 

If necessary it introduces
- `Vec K X` if `X` is fvar
-/
private partial def withVecImpl
  (K X : Expr) (k : Array Expr → MetaM α) : MetaM α := do
  let .some ⟨_u,K⟩ ← isTypeQ K | throwError "invalid type {← ppExpr K}"
  loop K X #[] k
where
  loop {u} (K : Q(Type $u)) (X : Expr) (acc : Array Expr) (k : Array Expr → MetaM α) : MetaM α := do
    let cls ← mkAppM ``Vec #[K, X]
    match ← synthInstance? cls with
    | .some _ => 
      k acc
    | none => 
      match X with
      | .forallE _ _ Y _ => 
        if Y.hasLooseBVars then
          throwError "can't extend context for dependent type `{← ppExpr X}`"
        loop K Y acc k
      | .app .. => 
        if X.isAppOfArity' ``Prod 2 then
          let X₁ := X.getArg! 0
          let X₂ := X.getArg! 1
          loop K X₁ acc (fun acc' => loop K X₂ acc' k)
        else
          throwError "dont' know how to extend context for the type `{← ppExpr X}`"
      | .fvar _ => 
        withLocalDecl (← mkAuxName `inst 0) .instImplicit cls fun inst => 
          k (acc.push inst)
      | _ => 
        throwError "dont' know how to extend context for the type `{← ppExpr X}`"


/-- Modifies the local context such that `X` has instance `Vec K X`

All newly introduced free variables are passed to k. 

If necessary it introduces
- `Vec K X` if `X` is fvar
-/
def withVec (K X : Expr) (k : Array Expr → n α) : n α := do
  map1MetaM (fun k => withVecImpl K X k) k

/-- Modifies the local context such that all `Xs := #[X₁,...,Xₙ]` have instance `Vec K Xᵢ`

All newly introduced free variables are passed to k. 

If necessary it introduces
- `Vec K X` if `X` is fvar
-/
def withVecs {α : Type _}
  (K : Expr) (Xs : Array Expr) (k : Array Expr → n α) : n α := do
  loop Xs.toList #[]
where 
  loop (Xs' : List Expr) (acc : Array Expr) : n α :=
    match Xs' with
    | [] => k acc
    | X :: Xs => withVec K X (fun acc' => loop Xs (acc ++ acc'))



private partial def withSemiInnerProductSpaceImpl
  (K X : Expr) (k : Array Expr → MetaM α) : MetaM α := do
  let .some ⟨_u,K⟩ ← isTypeQ K | throwError "invalid type {← ppExpr K}"
  loop K X #[] k
where
  loop {u} (K : Q(Type $u)) (X : Expr) (acc : Array Expr) (k : Array Expr → MetaM α) : MetaM α := do
    let cls ← mkAppM ``SemiInnerProductSpace #[K, X]
    match ← synthInstance? cls with
    | .some _ => k acc
    | none => 
      match X with
      | .forallE _ I Y _ => 
        if Y.hasLooseBVars then
          throwError "can't extend context for dependent type `{← ppExpr X}`"
        withEnumType I u u (fun acc' => loop K Y (acc ++ acc') k)
      | .app .. => 
        if X.isAppOfArity' ``Prod 2 then
          let X₁ := X.getArg! 0
          let X₂ := X.getArg! 1
          loop K X₁ acc (fun acc' => loop K X₂ acc' k)
        else
          throwError "dont' know how to extend context for the type `{← ppExpr X}`"
      | .fvar _ => 
        -- try to upgrade Vec to SemiInnerProductSpace
        let vecX ← mkAppM ``Vec #[K,X]
        let lctx ← getLCtx
        let vecId? ← lctx.findDeclM? 
          (fun decl => do 
            pure <| if (← isDefEq decl.type vecX) then .some (decl.fvarId) else .none)
        match vecId? with
        | .some vecId => 
            let lctx' := lctx.modifyLocalDecl vecId
              fun decl => decl.setType cls
            let insts ← getLocalInstances
            let insts' := insts.erase vecId 
              |>.push {className := ``SemiInnerProductSpace, fvar := .fvar vecId}
            withLCtx lctx' insts' (k acc)
        | .none => 
          withLocalDecl (← mkAuxName `inst 0) .instImplicit cls fun inst => 
            k (acc.push inst)
      | _ => 
        throwError "dont' know how to extend context for the type `{← ppExpr X}`"


/-- Modifies the local context such that `X` has instance `SemiInnerProductSpace K X`

All newly introduced free variables are passed to k. 

If necessary it introduces
- `EnumType I` for `X = I → Y` 
- `SemiInnerProductSpace K X` if `X` is fvar

It modifies existing instances 
- `Vec K X` to `SemiInnerProductSpace K X`
-/
def withSemiInnerProductSpace (K X : Expr) (k : Array Expr → n α) : n α := do
  map1MetaM (fun k => withSemiInnerProductSpaceImpl K X k) k
  

def withSemiInnerProductSpaces 
  (K : Expr) (Xs : Array Expr) (k : Array Expr → n α) : n α := do
  loop Xs.toList #[]
where 
  loop (Xs' : List Expr) (acc : Array Expr) : n α :=
    match Xs' with
    | [] => k acc
    | X :: Xs => withSemiInnerProductSpace K X (fun acc' => loop Xs (acc ++ acc'))


private partial def withSemiHilbertImpl
  (K X : Expr) (k : Array Expr → MetaM α) : MetaM α := do
  let .some ⟨_u,K⟩ ← isTypeQ K | throwError "invalid type {← ppExpr K}"
  loop K X #[] k
where
  loop {u} (K : Q(Type $u)) (X : Expr) (acc : Array Expr) (k : Array Expr → MetaM α) : MetaM α := do
    let cls ← mkAppM ``SemiHilbert #[K, X]
    match ← synthInstance? cls with
    | .some _ => k acc
    | none => 
      match X with
      | .forallE _ I Y _ => 
        if Y.hasLooseBVars then
          throwError "can't extend context for dependent type `{← ppExpr X}`"
        withEnumType I u u (fun acc' => loop K Y (acc ++ acc') k)
      | .app .. => 
        if X.isAppOfArity' ``Prod 2 then
          let X₁ := X.getArg! 0
          let X₂ := X.getArg! 1
          loop K X₁ acc (fun acc' => loop K X₂ acc' k)
        else
          throwError "dont' know how to extend context for the type `{← ppExpr X}`"
      | .fvar _ => 
        -- try to upgrade Vec or SemiInnerProductSpace to SemiHilbert
        let vecX ← mkAppM ``Vec #[K,X]
        let innerX ← mkAppM ``SemiInnerProductSpace #[K,X]
        let lctx ← getLCtx
        let id? ← lctx.findDeclM? 
          (fun decl => do 
            pure <| if (← isDefEq decl.type vecX) || (← isDefEq decl.type innerX) 
                    then .some (decl.fvarId) else .none)
        match id? with
        | .some id => 
            let lctx' := lctx.modifyLocalDecl id
              fun decl => decl.setType cls
            let insts ← getLocalInstances
            let insts' := insts.erase id 
              |>.push {className := ``SemiHilbert, fvar := .fvar id}
            withLCtx lctx' insts' (k acc)
        | .none => 
          withLocalDecl (← mkAuxName `inst 0) .instImplicit cls fun inst => 
            k (acc.push inst)
      | _ => 
        throwError "dont' know how to extend context for the type `{← ppExpr X}`"


/-- Modifies the local context such that `X` has instance `SemiHilbert K X`

All newly introduced free variables are passed to k. 

If necessary it introduces
- `EnumType I` for `X = I → Y` 
- `SemiHilbert K X` if `X` is fvar

It modifies
- instance `Vec K X` to `SemiHilbert K X`
- instance `SemiInnerProductSpace K X` to `SemiHilbert K X`
-/
def withSemiHilbert (K X : Expr) (k : Array Expr → n α) : n α := do
  map1MetaM (fun k => withSemiHilbertImpl K X k) k
  

def withSemiHilberts 
  (K : Expr) (Xs : Array Expr) (k : Array Expr → n α) : n α := do
  loop Xs.toList #[]
where 
  loop (Xs' : List Expr) (acc : Array Expr) : n α :=
    match Xs' with
    | [] => k acc
    | X :: Xs => withSemiHilbert K X (fun acc' => loop Xs (acc ++ acc'))
