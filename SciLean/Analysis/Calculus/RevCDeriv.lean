-- import SciLean.Analysis.Convenient.HasAdjDiff
-- import SciLean.Analysis.Convenient.SemiAdjoint
-- import SciLean.Analysis.FunctionSpaces.SmoothLinearMap

-- import SciLean.Data.StructType.Algebra

-- set_option linter.unusedVariables false

-- namespace SciLean

-- set_option deprecated.oldSectionVars true

-- variable
--   (K I : Type _) [RCLike K]
--   {X : Type _} [SemiInnerProductSpace K X]
--   {Y : Type _} [SemiInnerProductSpace K Y]
--   {Z : Type _} [SemiInnerProductSpace K Z]
--   {W : Type _} [SemiInnerProductSpace K W]
--   {ι : Type _} [IndexType ι nι] [DecidableEq ι]
--   {κ : Type _} [IndexType κ nκ] [DecidableEq κ]
--   {E : Type _} {EI : I → Type _}
--   [StructType E I EI] [IndexType I NI] [DecidableEq I]
--   [SemiInnerProductSpace K E] [∀ i, SemiInnerProductSpace K (EI i)]
--   [SemiInnerProductSpaceStruct K E I EI]
--   {F J : Type _} {FJ : J → Type _}
--   [StructType F J FJ] [IndexType J NJ] [DecidableEq J]
--   [SemiInnerProductSpace K F] [∀ j, SemiInnerProductSpace K (FJ j)]
--   [SemiInnerProductSpaceStruct K F J FJ]


-- @[fun_trans]
-- noncomputable
-- def revCDeriv
--   (f : X → Y) (x : X) : Y×(Y→X) :=
--   (f x, semiAdjoint K (cderiv K f x))

-- @[fun_trans]
-- noncomputable
-- def revCDerivUpdate
--   (f : X → Y) (x : X) : Y×(Y→X→X) :=
--   let ydf := revCDeriv K f x
--   (ydf.1, fun dy dx => dx + ydf.2 dy)

-- @[fun_trans]
-- noncomputable
-- def revCDerivProj [DecidableEq I]
--   (f : X → E) (x : X) : E×((i : I)→EI i→X) :=
--   let ydf' := revCDeriv K f x
--   (ydf'.1, fun i de =>
--     ydf'.2 (oneHot i de))

-- @[fun_trans]
-- noncomputable
-- def revCDerivProjUpdate [DecidableEq I]
--   (f : X → E) (x : X) : E×((i : I)→EI i→X→X) :=
--   let ydf' := revCDerivProj K I f x
--   (ydf'.1, fun i de dx => dx + ydf'.2 i de)


-- noncomputable
-- abbrev revCDeriv' (f : X → Y) (x : X) : Y×(Y ⊸[K] X) :=
--   let ydf := revCDeriv K f x
--   (ydf.1, ⟨fun dy => ydf.2 dy, by simp (config:={zetaDelta:=true}) [revCDeriv]; fun_prop⟩)


-- noncomputable
-- abbrev gradient (f : X → Y) (x : X) : (Y → X):= (revCDeriv K f x).2

-- noncomputable
-- abbrev scalarGradient (f : X → K) (x : X) : X := (revCDeriv K f x).2 1


-- --------------------------------------------------------------------------------
-- -- simplification rules for individual components ------------------------------
-- --------------------------------------------------------------------------------

-- @[simp, simp_core]
-- theorem revCDeriv_fst (f : X → Y) (x : X)
--   : (revCDeriv K f x).1 = f x :=
-- by
--   rfl

-- @[simp, simp_core]
-- theorem revCDeriv_snd_zero (f : X → Y) (x : X)
--   : (revCDeriv K f x).2 0 = 0 :=
-- by
--   simp[revCDeriv]

-- @[simp, simp_core]
-- theorem revCDerivUpdate_fst (f : X → Y) (x : X)
--   : (revCDerivUpdate K f x).1 = f x :=
-- by
--   rfl

-- @[simp, simp_core]
-- theorem revCDerivUpdate_snd_zero (f : X → Y) (x dx : X)
--   : (revCDerivUpdate K f x).2 0 dx = dx :=
-- by
--   simp[revCDerivUpdate]

-- @[simp, simp_core]
-- theorem revCDerivUpdate_snd_zero' (f : X → Y) (x : X) (dy : Y)
--   : (revCDerivUpdate K f x).2 dy 0 = (revCDeriv K f x).2 dy :=
-- by
--   simp[revCDerivUpdate]


-- @[simp, simp_core]
-- theorem revCDerivProj_fst (f : X → E) (x : X)
--   : (revCDerivProj K (I:=I) f x).1 = f x :=
-- by
--   rfl

-- @[simp, simp_core]
-- theorem revCDerivProj_snd_zero (f : X → E) (x : X) (i : I)
--   : (revCDerivProj K I f x).2 i 0 = 0 :=
-- by
--   simp[revCDerivProj]

-- @[simp, simp_core]
-- theorem revCDerivProjUpdate_fst (f : X → E) (x : X)
--   : (revCDerivProjUpdate K I f x).1 = f x :=
-- by
--   rfl

-- @[simp, simp_core]
-- theorem revCDerivProjUpdate_snd_zero (f : X → E) (x dx : X) (i : I)
--   : (revCDerivProjUpdate K I f x).2 i 0 dx = dx :=
-- by
--   simp[revCDerivProjUpdate]

-- @[simp, simp_core]
-- theorem revCDerivProjUpdate_snd_zero' (f : X → Y) (x : X) (dy : Y)
--   : (revCDerivUpdate K f x).2 dy 0 = (revCDeriv K f x).2 dy :=
-- by
--   simp[revCDerivUpdate]


-- --------------------------------------------------------------------------------
-- -- Lambda calculus rules for revCDeriv ------------------------------------------
-- --------------------------------------------------------------------------------

-- namespace revCDeriv

-- @[fun_trans]
-- theorem id_rule :
--     revCDeriv K (fun x : X => x) = fun x => (x, fun dx => dx) := by
--   unfold revCDeriv
--   fun_trans

-- @[fun_trans]
-- theorem const_rule (y : Y) :
--     revCDeriv K (fun _ : X => y) = fun x => (y, fun _ => 0) := by
--   unfold revCDeriv
--   fun_trans

-- @[fun_trans]
-- theorem comp_rule
--     (f : Y → Z) (g : X → Y)
--     (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     revCDeriv K (fun x : X => f (g x))
--     =
--     fun x =>
--       let ydg := revCDeriv K g x
--       let zdf := revCDeriv K f ydg.1
--       (zdf.1,
--        fun dz =>
--          let dy := zdf.2 dz
--          ydg.2 dy)  := by
--   unfold revCDeriv
--   fun_trans


-- example
--     (f : X → Y → Z) (g : X → Y)
--     -- (hf : HasAdjDiff K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : HasAdjDiff K g) :
--     (hf : HasAdjDiff K ↿f) (hg : HasAdjDiff K g) :
--     HasSemiAdjoint K fun dx => SciLean.cderiv K (fun xy => f xy.1 xy.2) (x, g x) dx := by fun_prop

-- example (f : X → Y → Z) (hf : HasAdjDiff K ↿f) :
--    HasAdjDiff K (fun xy : X×Y => f xy.1 xy.2) := by fun_prop

-- @[fun_trans]
-- theorem let_rule
--     (f : X → Y → Z) (g : X → Y)
--     (hf : HasAdjDiff K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : HasAdjDiff K g) :
--     -- todo: for some reason `fun_prop` does not see (hf : HasAdjDiff K ↿f)
--     -- (hf : HasAdjDiff K ↿f) (hg : HasAdjDiff K g) :
--     revCDeriv K (fun x : X => let y := g x; f x y)
--     =
--     fun x =>
--       let ydg := revCDerivUpdate K g x
--       let zdf := revCDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
--       (zdf.1,
--        fun dz =>
--          let dxdy := zdf.2 dz
--          let dx := ydg.2 dxdy.2 dxdy.1
--          dx)  := by
--   unfold revCDerivUpdate revCDeriv
--   fun_trans

-- -- @[fun_trans]
-- -- theorem apply_rule (i : I) :
-- --     revCDeriv K (fun (x : (i:I) → EI i) => x i)
-- --     =
-- --     fun x =>
-- --       (x i, fun dxi => oneHot i dxi) := by
-- --   unfold revCDeriv
-- --   fun_trans; simp[oneHot]

-- -- @[fun_trans]
-- -- theorem pi_rule
-- --     (f :  X → (i : I) → EI i) (hf : ∀ i, HasAdjDiff K (f · i)) :
-- --     (revCDeriv K fun (x : X) (i : I) => f x i)
-- --     =
-- --     fun x =>
-- --       let xdf := fun i => revCDerivUpdate K (f · i) x
-- --       (fun i => (xdf i).1,
-- --        fun dy =>
-- --          IndexType.foldl (fun dx i => (xdf i).2 (dy i) dx) 0) := by
-- --   unfold revCDeriv
-- --   fun_trans;
-- --   funext x; simp
-- --   rw[cderiv.pi_rule (hf:=by fun_prop)]; fun_trans
-- --   simp[revCDerivUpdate,revCDeriv,sum]
-- --   sorry_proof

-- end revCDeriv


-- --------------------------------------------------------------------------------
-- -- Lambda calculus rules for revCDerivUpdate ------------------------------------
-- --------------------------------------------------------------------------------

-- namespace revCDerivUpdate

-- @[fun_trans]
-- theorem id_rule :
--     revCDerivUpdate K (fun x : X => x) = fun x => (x, fun dx' dx => dx + dx') := by
--   unfold revCDerivUpdate
--   fun_trans

-- @[fun_trans]
-- theorem const_rule (y : Y) :
--     revCDerivUpdate K (fun _ : X => y) = fun x => (y, fun _ dx => dx) := by
--   unfold revCDerivUpdate
--   fun_trans

-- @[fun_trans]
-- theorem comp_rule
--     (f : Y → Z) (g : X → Y)
--     (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     revCDerivUpdate K (fun x : X => f (g x))
--     =
--     fun x =>
--       let ydg := revCDerivUpdate K g x
--       let zdf := revCDeriv K f ydg.1
--       (zdf.1,
--        fun dz dx =>
--          let dy := zdf.2 dz
--          ydg.2 dy dx)  := by
--   unfold revCDerivUpdate
--   fun_trans

-- @[fun_trans]
-- theorem let_rule
--     (f : X → Y → Z) (g : X → Y)
--     (hf : HasAdjDiff K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : HasAdjDiff K g) :
--     revCDerivUpdate K (fun x : X => let y := g x; f x y)
--     =
--     fun x =>
--       let ydg := revCDerivUpdate K g x
--       let zdf := revCDerivUpdate K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
--       (zdf.1,
--        fun dz dx =>
--          let dxdy := zdf.2 dz (dx, 0)
--          let dx := ydg.2 dxdy.2 dxdy.1
--          dx)  := by
--   unfold revCDerivUpdate
--   fun_trans [revCDerivUpdate,revCDeriv,add_assoc]


-- -- @[fun_trans]
-- -- theorem apply_rule (i : I) :
-- --     revCDerivUpdate K (fun (x : (i:I) → EI i) => x i)
-- --     =
-- --     fun x =>
-- --       (x i, fun dxi dx => structModify i (fun dxi' => dxi' + dxi) dx) := by
-- --   unfold revCDerivUpdate
-- --   fun_trans

-- -- @[fun_trans]
-- -- theorem pi_rule
-- --     (f :  X → (i : I) → EI i) (hf : ∀ i, HasAdjDiff K (f · i)) :
-- --     (revCDerivUpdate K fun (x : X) (i : I) => f x i)
-- --     =
-- --     fun x =>
-- --       let xdf := fun i => revCDerivUpdate K (f · i) x
-- --       (fun i => (xdf i).1,
-- --        fun dy dx =>
-- --          IndexType.foldl (fun dx i => (xdf i).2 (dy i) dx) dx) := by
-- --   unfold revCDerivUpdate
-- --   funext x
-- --   rw[revCDeriv.pi_rule (hf:=by fun_prop)]
-- --   simp
-- --   sorry_proof


-- end revCDerivUpdate


-- --------------------------------------------------------------------------------
-- -- Lambda calculus rules for revCDerivProj ------------------------------------
-- --------------------------------------------------------------------------------

-- namespace revCDerivProj

-- @[fun_trans]
-- theorem id_rule :
--     revCDerivProj K I (fun x : E => x)
--     =
--     fun x =>
--       (x,
--        fun i de =>
--          oneHot i de) := by
--   unfold revCDerivProj; fun_trans

-- @[fun_trans]
-- theorem const_rule (x : E)
--   : revCDerivProj K I (fun _ : Y => x)
--     =
--     fun _ =>
--       (x,
--        fun i (de : EI i) => 0) := by
--   unfold revCDerivProj; fun_trans

-- -- @[fun_trans]
-- -- theorem apply_rule [DecidableEq I] (i : ι) :
-- --     revCDerivProj K I (fun (f : ι → E) => f i)
-- --     =
-- --     fun f : ι → E =>
-- --       (f i, fun j dxj => oneHot (X:=ι→E) (I:=ι×I) (i,j) dxj) :=
-- -- by
-- --   unfold revCDerivProj;
-- --   fun_trans; simp[oneHot]
-- --   funext x; simp; funext j de i'
-- --   if h:i=i' then
-- --     subst h
-- --     simp; congr; funext j'
-- --     if h':j=j' then
-- --       subst h'
-- --       simp
-- --     else
-- --       simp[h']
-- --   else
-- --     simp[h]

-- @[fun_trans]
-- theorem comp_rule
--     (f : Y → E) (g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     revCDerivProj K I (fun x => f (g x))
--     =
--     fun x =>
--       let ydg' := revCDeriv K g x
--       let zdf' := revCDerivProj K I f ydg'.1
--       (zdf'.1,
--        fun i de =>
--          ydg'.2 (zdf'.2 i de)) := by
--   unfold revCDerivProj; fun_trans

-- @[fun_trans]
-- theorem let_rule
--     (f : X → Y → E) (g : X → Y)
--     (hf : HasAdjDiff K (fun (x,y) => f x y)) (hg : HasAdjDiff K g) :
--     revCDerivProj K I (fun x => let y := g x; f x y)
--     =
--     fun x =>
--       let ydg' := revCDerivUpdate K g x
--       let zdf' := revCDerivProj K I (fun (x,y) => f x y) (x,ydg'.1)
--       (zdf'.1,
--        fun i dei =>
--          let dxy := zdf'.2 i dei
--          ydg'.2 dxy.2 dxy.1) := by
--   unfold revCDerivProj revCDerivUpdate revCDeriv; fun_trans

-- -- @[fun_trans]
-- -- theorem pi_rule
-- --     (f :  X → ι → Y) (hf : ∀ i, HasAdjDiff K (f · i)) :
-- --     (revCDerivProj K Unit fun (x : X) (i : ι) => f x i)
-- --     =
-- --     fun x =>
-- --       let ydf := fun i => revCDerivUpdate K (f · i) x
-- --       (fun i => (ydf i).1,
-- --        fun _ df =>
-- --          IndexType.foldl (fun dx i => (ydf i).2 (df i) dx) (0 : X)) := by
-- --   unfold revCDerivProj
-- --   fun_trans
-- --   funext x; simp; funext i de
-- --   rw[revCDeriv.pi_rule (hf:=by fun_prop)]; simp[oneHot]

-- end revCDerivProj


-- --------------------------------------------------------------------------------
-- -- Lambda calculus rules for revCDerivProjUpdate --------------------------------
-- --------------------------------------------------------------------------------

-- namespace revCDerivProjUpdate

-- @[fun_trans]
-- theorem id_rule
--   : revCDerivProjUpdate K I (fun x : E => x)
--     =
--     fun x =>
--       (x,
--        fun i de dx =>
--          structModify i (fun ei => ei + de) dx) :=
-- by
--   funext x
--   simp[revCDerivProjUpdate, revCDerivProj.id_rule]

-- @[fun_trans]
-- theorem const_rule (x : E)
--   : revCDerivProjUpdate K I (fun _ : Y => x)
--     =
--     fun _ =>
--       (x,
--        fun i de dx => dx) :=
-- by
--   unfold revCDerivProjUpdate; simp[revCDerivProj.const_rule]

-- @[fun_trans]
-- theorem comp_rule
--   (f : Y → E) (g : X → Y)
--   (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
--   : revCDerivProjUpdate K I (fun x => f (g x))
--     =
--     fun x =>
--       let ydg' := revCDerivUpdate K g x
--       let zdf' := revCDerivProj K I f ydg'.1
--       (zdf'.1,
--        fun i de dx =>
--          ydg'.2 (zdf'.2 i de) dx) :=
-- by
--   funext x
--   simp[revCDerivProjUpdate,revCDerivProj.comp_rule _ _ _ _ hf hg]
--   rfl

-- @[fun_trans]
-- theorem let_rule
--   (f : X → Y → E) (g : X → Y)
--   (hf : HasAdjDiff K (fun (x,y) => f x y)) (hg : HasAdjDiff K g)
--   : revCDerivProjUpdate K I (fun x => let y := g x; f x y)
--     =
--     fun x =>
--       let ydg' := revCDerivUpdate K g x
--       let zdf' := revCDerivProjUpdate K I (fun (x,y) => f x y) (x,ydg'.1)
--       (zdf'.1,
--        fun i dei dx =>
--          let dxy := zdf'.2 i dei (dx,0)
--          ydg'.2 dxy.2 dxy.1) :=
-- by
--   unfold revCDerivProjUpdate
--   simp [revCDerivProj.let_rule _ _ _ _ hf hg,add_assoc,add_comm,revCDerivUpdate]

-- -- @[fun_trans]
-- -- theorem apply_rule [DecidableEq I] (i : ι)
-- --   : revCDerivProjUpdate K I (fun (f : ι → E) => f i)
-- --     =
-- --     fun f =>
-- --       (f i, fun j dxj df i' =>
-- --         if i=i' then
-- --           structModify j (fun xj => xj + dxj) (df i')
-- --         else
-- --           df i') :=
-- -- by
-- --   funext x;
-- --   unfold revCDerivProjUpdate
-- --   fun_trans
-- --   funext j dxj f i'
-- --   apply structExt (I:=I)
-- --   intro j'
-- --   if h :i'=i then
-- --     subst h; simp
-- --   else
-- --     have h' : i≠i' := by intro h''; simp[h''] at h
-- --     simp[h,h',Function.update]

-- -- @[fun_trans]
-- -- theorem pi_rule
-- --     (f :  X → ι → Y) (hf : ∀ i, HasAdjDiff K (f · i)) :
-- --     (revCDerivProjUpdate K Unit fun (x : X) (i : ι) => f x i)
-- --     =
-- --     fun x =>
-- --       let ydf := fun i => revCDerivUpdate K (f · i) x
-- --       (fun i => (ydf i).1,
-- --        fun _ df dx =>
-- --          IndexType.foldl (fun dx i => (ydf i).2 (df i) dx) dx) :=
-- -- by
-- --   unfold revCDerivProjUpdate
-- --   fun_trans
-- --   unfold revCDerivProj
-- --   funext x; simp; funext i de dx
-- --   rw[revCDeriv.pi_rule (hf:=by fun_prop)]; simp[oneHot,revCDerivUpdate]
-- --   sorry_proof


-- end revCDerivProjUpdate


-- --------------------------------------------------------------------------------
-- --------------------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- end SciLean
-- open SciLean

-- set_option deprecated.oldSectionVars true
-- #exit
-- variable
--   {K : Type} [RCLike K]
--   {X : Type} [SemiInnerProductSpace K X]
--   {Y : Type} [SemiInnerProductSpace K Y]
--   {Z : Type} [SemiInnerProductSpace K Z]
--   {X' Xi : Type} {XI : Xi → Type} [StructType X' Xi XI] [IndexType X NXi] [DecidableEq Xi]
--   {Y' Yi : Type} {YI : Yi → Type} [StructType Y' Yi YI] [IndexType Y NYi] [DecidableEq Yi]
--   {Z' Zi : Type} {ZI : Zi → Type} [StructType Z' Zi ZI] [IndexType Z NZi] [DecidableEq Zi]
--   [SemiInnerProductSpace K X'] [∀ i, SemiInnerProductSpace K (XI i)] [SemiInnerProductSpaceStruct K X' Xi XI]
--   [SemiInnerProductSpace K Y'] [∀ i, SemiInnerProductSpace K (YI i)] [SemiInnerProductSpaceStruct K Y' Yi YI]
--   [SemiInnerProductSpace K Z'] [∀ i, SemiInnerProductSpace K (ZI i)] [SemiInnerProductSpaceStruct K Z' Zi ZI]
--   {W : Type} [SemiInnerProductSpace K W]
--   {ι : Type} [IndexType ι nι]



-- -- Prod.mk ---------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- @[fun_trans]
-- theorem Prod.mk.arg_fstsnd.revCDeriv_rule
--     (g : X → Y) (f : X → Z) (hg : HasAdjDiff K g) (hf : HasAdjDiff K f) :
--     revCDeriv K (fun x => (g x, f x))
--     =
--     fun x =>
--       let ydg := revCDeriv K g x
--       let zdf := revCDerivUpdate K f x
--       ((ydg.1,zdf.1),
--        fun dyz =>
--          let dx := ydg.2 dyz.1
--          zdf.2 dyz.2 dx) := by
--   unfold revCDerivUpdate; unfold revCDeriv; simp; fun_trans

-- @[fun_trans]
-- theorem Prod.mk.arg_fstsnd.revCDerivUpdate_rule
--   (g : X → Y) (f : X → Z)
--   (hg : HasAdjDiff K g) (hf : HasAdjDiff K f)
--   : revCDerivUpdate K (fun x => (g x, f x))
--     =
--     fun x =>
--       let ydg := revCDerivUpdate K g x
--       let zdf := revCDerivUpdate K f x
--       ((ydg.1,zdf.1),
--        fun dyz dx =>
--          let dx := ydg.2 dyz.1 dx
--          zdf.2 dyz.2 dx) :=
-- by
--   unfold revCDerivUpdate; fun_trans; simp[add_assoc, revCDerivUpdate]

-- @[fun_trans]
-- theorem Prod.mk.arg_fstsnd.revCDerivProj_rule
--     (g : X → Y') (f : X → Z')
--     (hg : HasAdjDiff K g) (hf : HasAdjDiff K f) :
--     revCDerivProj K (Yi⊕Zi) (fun x => (g x, f x))
--     =
--     fun x =>
--       let ydg := revCDerivProj K Yi g x
--       let zdf := revCDerivProj K Zi f x
--       ((ydg.1,zdf.1),
--        fun i dyz =>
--          match i with
--          | .inl j => ydg.2 j dyz
--          | .inr j => zdf.2 j dyz) := by
--   unfold revCDerivProj
--   funext x; fun_trans; simp[revCDerivUpdate]
--   funext i dyz
--   induction i <;>
--     { simp[oneHot,structMake]
--       apply congr_arg
--       congr; funext i; congr; funext h
--       subst h; rfl
--     }

-- @[fun_trans]
-- theorem Prod.mk.arg_fstsnd.revCDerivProjUpdate_rule
--     (g : X → Y') (f : X → Z')
--     (hg : HasAdjDiff K g) (hf : HasAdjDiff K f) :
--     revCDerivProjUpdate K (Yi⊕Zi) (fun x => (g x, f x))
--     =
--     fun x =>
--       let ydg := revCDerivProjUpdate K Yi g x
--       let zdf := revCDerivProjUpdate K Zi f x
--       ((ydg.1,zdf.1),
--        fun i dyz dx =>
--          match i with
--          | .inl j => ydg.2 j dyz dx
--          | .inr j => zdf.2 j dyz dx) := by
--   unfold revCDerivProjUpdate
--   funext x; fun_trans
--   funext i de dx
--   induction i <;> simp


-- -- Prod.fst --------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- @[fun_trans]
-- theorem Prod.fst.arg_self.revCDeriv_rule
--     (f : X → Y×Z) (hf : HasAdjDiff K f) :
--     revCDeriv K (fun x => (f x).1)
--     =
--     fun x =>
--       let yzdf := revCDerivProj K (Unit⊕Unit) f x
--       (yzdf.1.1, fun dy => yzdf.2 (.inl ()) dy) := by
--   unfold revCDerivProj; unfold revCDeriv
--   fun_trans

-- @[fun_trans]
-- theorem Prod.fst.arg_self.revCDerivUpdate_rule
--     (f : X → Y×Z) (hf : HasAdjDiff K f) :
--     revCDerivUpdate K (fun x => (f x).1)
--     =
--     fun x =>
--       let yzdf := revCDerivProjUpdate K (Unit⊕Unit) f x
--       (yzdf.1.1, fun dy dx => yzdf.2 (.inl ()) dy dx) := by
--   unfold revCDerivProjUpdate; unfold revCDerivUpdate;
--   fun_trans

-- @[fun_trans]
-- theorem Prod.fst.arg_self.revCDerivProj_rule
--     (f : W → X'×Y) (hf : HasAdjDiff K f) :
--     revCDerivProj K Xi (fun x => (f x).1)
--     =
--     fun w =>
--       let xydf := revCDerivProj K (Xi⊕Unit) f w
--       (xydf.1.1,
--        fun i dxy => xydf.2 (.inl i) dxy) := by
--   unfold revCDerivProj
--   funext x; fun_trans[revCDerivProj]

-- @[fun_trans]
-- theorem Prod.fst.arg_self.revCDerivProjUpdate_rule
--     (f : W → X'×Y) (hf : HasAdjDiff K f) :
--     revCDerivProjUpdate K Xi (fun x => (f x).1)
--     =
--     fun w =>
--       let xydf := revCDerivProjUpdate K (Xi⊕Unit) f w
--       (xydf.1.1,
--        fun i dxy dw => xydf.2 (.inl i) dxy dw) := by
--   unfold revCDerivProjUpdate
--   funext x; fun_trans


-- -- Prod.snd --------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- @[fun_trans]
-- theorem Prod.snd.arg_self.revCDeriv_rule
--     (f : X → Y×Z) (hf : HasAdjDiff K f) :
--     revCDeriv K (fun x => (f x).2)
--     =
--     fun x =>
--       let yzdf := revCDerivProj K (Unit⊕Unit) f x
--       (yzdf.1.2, fun dy => yzdf.2 (.inr ()) dy) := by
--   unfold revCDerivProj; unfold revCDeriv
--   fun_trans

-- @[fun_trans]
-- theorem Prod.snd.arg_self.revCDerivUpdate_rule
--     (f : X → Y×Z) (hf : HasAdjDiff K f) :
--     revCDerivUpdate K (fun x => (f x).2)
--     =
--     fun x =>
--       let yzdf := revCDerivProjUpdate K (Unit⊕Unit) f x
--       (yzdf.1.2, fun dy dx => yzdf.2 (.inr ()) dy dx) := by
--   unfold revCDerivProjUpdate; unfold revCDerivUpdate
--   fun_trans

-- @[fun_trans]
-- theorem Prod.snd.arg_self.revCDerivProj_rule
--     (f : W → X×Y') (hf : HasAdjDiff K f) :
--     revCDerivProj K Yi (fun x => (f x).2)
--     =
--     fun w =>
--       let xydf := revCDerivProj K (Unit⊕Yi) f w
--       (xydf.1.2,
--        fun i dxy => xydf.2 (.inr i) dxy) := by
--   unfold revCDerivProj
--   funext x; fun_trans[revCDerivProj]

-- @[fun_trans]
-- theorem Prod.snd.arg_self.revCDerivProjUpdate_rule
--     (f : W → X×Y') (hf : HasAdjDiff K f) :
--     revCDerivProjUpdate K Yi (fun x => (f x).2)
--     =
--     fun w =>
--       let xydf := revCDerivProjUpdate K (Unit⊕Yi) f w
--       (xydf.1.2,
--        fun i dxy dw => xydf.2 (.inr i) dxy dw) := by
--   unfold revCDerivProjUpdate
--   funext x; fun_trans


-- -- HAdd.hAdd -------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- @[fun_trans]
-- theorem HAdd.hAdd.arg_a0a1.revCDeriv_rule
--     (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDeriv K fun x => f x + g x)
--     =
--     fun x =>
--       let ydf := revCDeriv K f x
--       let ydg := revCDerivUpdate K g x
--       (ydf.1 + ydg.1,
--        fun dy =>
--          let dx := ydf.2 dy
--          ydg.2 dy dx) := by
--   unfold revCDerivUpdate; unfold revCDeriv; simp; fun_trans

-- @[fun_trans]
-- theorem HAdd.hAdd.arg_a0a1.revCDerivUpdate_rule
--     (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDerivUpdate K fun x => f x + g x)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       let ydg := revCDerivUpdate K g x
--       (ydf.1 + ydg.1,
--        fun dy dx =>
--          let dx := ydf.2 dy dx
--          ydg.2 dy dx) := by
--   unfold revCDerivUpdate
--   fun_trans; funext x; simp[add_assoc,revCDerivUpdate]

-- @[fun_trans]
-- theorem HAdd.hAdd.arg_a0a1.revCDerivProj_rule
--     (f g : X → Y') (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDerivProj K Yi fun x => f x + g x)
--     =
--     fun x =>
--       let ydf := revCDerivProj K Yi f x
--       let ydg := revCDerivProjUpdate K Yi g x
--       (ydf.1 + ydg.1,
--        fun i dy =>
--          let dx := ydf.2 i dy
--          (ydg.2 i dy dx)) := by
--   unfold revCDerivProjUpdate; unfold revCDerivProj
--   fun_trans; simp[revCDerivUpdate]

-- @[fun_trans]
-- theorem HAdd.hAdd.arg_a0a1.revCDerivProjUpdate_rule
--     (f g : X → Y') (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDerivProjUpdate K Yi fun x => f x + g x)
--     =
--     fun x =>
--       let ydf := revCDerivProjUpdate K Yi f x
--       let ydg := revCDerivProjUpdate K Yi g x
--       (ydf.1 + ydg.1,
--        fun i dy dx =>
--          let dx := ydf.2 i dy dx
--          ydg.2 i dy dx) := by
--   unfold revCDerivProjUpdate
--   fun_trans; simp[revCDerivProjUpdate, add_assoc]


-- -- HSub.hSub -------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- @[fun_trans]
-- theorem HSub.hSub.arg_a0a1.revCDeriv_rule
--     (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDeriv K fun x => f x - g x)
--     =
--     fun x =>
--       let ydf := revCDeriv K f x
--       let ydg := revCDerivUpdate K g x
--       (ydf.1 - ydg.1,
--        fun dy =>
--          let dx := ydf.2 dy
--          let dy' := -dy
--          ydg.2 dy' dx) := by
--   unfold revCDerivUpdate; unfold revCDeriv;
--   fun_trans
--   funext x; simp; funext dy; simp only [neg_pull, ← sub_eq_add_neg]

-- @[fun_trans]
-- theorem HSub.hSub.arg_a0a1.revCDerivUpdate_rule
--     (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDerivUpdate K fun x => f x - g x)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       let ydg := revCDerivUpdate K g x
--       (ydf.1 - ydg.1,
--        fun dy dx =>
--          let dx := ydf.2 dy dx
--          let dy' := -dy
--          ydg.2 dy' dx) := by
--   unfold revCDerivUpdate
--   fun_trans; funext x; simp[add_assoc,revCDerivUpdate]

-- @[fun_trans]
-- theorem HSub.hSub.arg_a0a1.revCDerivProj_rule
--     (f g : X → Y') (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDerivProj K Yi fun x => f x - g x)
--     =
--     fun x =>
--       let ydf := revCDerivProj K Yi f x
--       let ydg := revCDerivProjUpdate K Yi g x
--       (ydf.1 - ydg.1,
--        fun i dy =>
--          let dx := ydf.2 i dy
--          let dy' := -dy
--          (ydg.2 i dy' dx)) := by
--   unfold revCDerivProjUpdate; unfold revCDerivProj
--   fun_trans; simp[revCDerivUpdate, revCDeriv]


-- @[fun_trans]
-- theorem HSub.hSub.arg_a0a1.revCDerivProjUpdate_rule
--     (f g : X → Y') (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDerivProjUpdate K Yi fun x => f x - g x)
--     =
--     fun x =>
--       let ydf := revCDerivProjUpdate K Yi f x
--       let ydg := revCDerivProjUpdate K Yi g x
--       (ydf.1 - ydg.1,
--        fun i dy dx =>
--          let dx := ydf.2 i dy dx
--          let dy' := -dy
--          ydg.2 i dy' dx) := by
--   unfold revCDerivProjUpdate
--   fun_trans; simp[revCDerivProjUpdate, revCDerivProj, revCDeriv,add_assoc]


-- -- Neg.neg ---------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- @[fun_trans]
-- theorem Neg.neg.arg_a0.revCDeriv_rule
--     (f : X → Y) (x : X) :
--     (revCDeriv K fun x => - f x) x
--     =
--     let ydf := revCDeriv K f x
--     (-ydf.1,
--      fun dy =>
--        let dx := ydf.2 dy
--        (-dx)) := by
--   unfold revCDeriv; simp; fun_trans

-- @[fun_trans]
-- theorem Neg.neg.arg_a0.revCDerivUpdate_rule
--     (f : X → Y) :
--     (revCDerivUpdate K fun x => - f x)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       (-ydf.1,
--        fun dy dx =>
--          let dy' := -dy
--          ydf.2 dy' dx) := by
--   unfold revCDerivUpdate; funext x; fun_trans; simp[neg_pull,revCDeriv]

-- @[fun_trans]
-- theorem Neg.neg.arg_a0.revCDerivProj_rule
--     (f : X → Y') :
--     (revCDerivProj K Yi fun x => - f x)
--     =
--     fun x =>
--       let ydf := revCDerivProj K Yi f x
--       (-ydf.1,
--        fun i dy =>
--          let dy' := -dy
--          ydf.2 i dy') := by
--   unfold revCDerivProj; fun_trans; simp[neg_push,revCDeriv]

-- @[fun_trans]
-- theorem Neg.neg.arg_a0.revCDerivProjUpdate_rule
--     (f : X → Y') :
--     (revCDerivProjUpdate K Yi fun x => - f x)
--     =
--     fun x =>
--       let ydf := revCDerivProjUpdate K Yi f x
--       (-ydf.1,
--        fun i dy dx =>
--          let dy' := -dy
--          ydf.2 i dy' dx) := by
--   unfold revCDerivProjUpdate; fun_trans


-- -- HMul.hmul -------------------------------------------------------------------
-- --------------------------------------------------------------------------------
-- open ComplexConjugate

-- @[fun_trans]
-- theorem HMul.hMul.arg_a0a1.revCDeriv_rule
--     (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDeriv K fun x => f x * g x)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       let zdg := revCDeriv K g x
--       (ydf.1 * zdg.1,
--        fun dx' =>
--          let dx₁ := (conj zdg.1 * dx')
--          let dx₂ := (conj ydf.1 * dx')
--          let dx := zdg.2 dx₂
--          ydf.2 dx₁ dx) := by
--   unfold revCDerivUpdate; unfold revCDeriv; simp; fun_trans
--   simp [smul_push]

-- @[fun_trans]
-- theorem HMul.hMul.arg_a0a1.revCDerivUpdate_rule
--     (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDerivUpdate K fun x => f x * g x)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       let zdg := revCDerivUpdate K g x
--       (ydf.1 * zdg.1,
--        fun dx' dx =>
--          let dx₁ := (conj zdg.1 * dx')
--          let dx₂ := (conj ydf.1 * dx')
--          let dx := zdg.2 dx₂ dx
--          ydf.2 dx₁ dx) := by
--   unfold revCDerivUpdate; simp; fun_trans
--   simp [smul_push,add_assoc,revCDerivUpdate]

-- @[fun_trans]
-- theorem HMul.hMul.arg_a0a1.revCDerivProj_rule
--     (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDerivProj K Unit fun x => f x * g x)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       let zdg := revCDeriv K g x
--       (ydf.1 * zdg.1,
--        fun _ dy =>
--          let dy₁ := (conj zdg.1)*dy
--          let dy₂ := (conj ydf.1)*dy
--          let dx := zdg.2 dy₂
--          ydf.2 dy₁ dx) := by
--   unfold revCDerivProj
--   fun_trans; simp[oneHot, structMake]

-- @[fun_trans]
-- theorem HMul.hMul.arg_a0a1.revCDerivProjUpdate_rule
--     (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDerivProjUpdate K Unit fun x => f x * g x)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       let zdg := revCDerivUpdate K g x
--       (ydf.1 * zdg.1,
--        fun _ dy dx =>
--          let dy₁ := (conj zdg.1)*dy
--          let dy₂ := (conj ydf.1)*dy
--          let dx := zdg.2 dy₂ dx
--          ydf.2 dy₁ dx) := by
--   unfold revCDerivProjUpdate
--   fun_trans; simp[revCDerivUpdate,add_assoc]


-- -- SMul.smul -------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- section SMulOnSemiHilbert

-- variable
--   {Y Yi : Type} {YI : Yi → Type} [StructType Y Yi YI] [IndexType Y NYi] [DecidableEq Yi]
--   [SemiHilbert K Y] [∀ i, SemiHilbert K (YI i)] [SemiInnerProductSpaceStruct K Y Yi YI]

-- @[fun_trans]
-- theorem HSMul.hSMul.arg_a0a1.revCDeriv_rule
--     (f : X → K) (g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDeriv K fun x => f x • g x)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       let zdg := revCDeriv K g x
--       (ydf.1 • zdg.1,
--        fun dy' =>
--          let dk := inner zdg.1 dy'
--          let dx := zdg.2 dy'
--          let dx := conj ydf.1 • dx
--          ydf.2 dk dx) := by
--   unfold revCDerivUpdate; unfold revCDeriv
--   fun_trans

-- @[fun_trans]
-- theorem HSMul.hSMul.arg_a0a1.revCDerivUpdate_rule
--     (f : X → K) (g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDerivUpdate K fun x => f x • g x)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       let zdg := revCDerivUpdate K g x
--       (ydf.1 • zdg.1,
--        fun dy dx =>
--          let dk := inner zdg.1 dy
--          let dy' := conj ydf.1 • dy
--          let dx := zdg.2 dy' dx
--          ydf.2 dk dx) := by
--   unfold revCDerivUpdate;
--   funext x; fun_trans; simp[mul_assoc,add_assoc,revCDerivUpdate,revCDeriv,smul_push]

-- @[fun_trans]
-- theorem HSMul.hSMul.arg_a0a1.revCDerivProj_rule
--     (f : X → K) (g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDerivProj K Yi fun x => f x • g x)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       let zdg := revCDerivProj K Yi g x
--       (ydf.1 • zdg.1,
--        fun i (dy : YI i) =>
--          let dk := inner (structProj zdg.1 i) dy
--          let dx := zdg.2 i dy
--          let dx := conj ydf.1•dx
--          ydf.2 dk dx) := by
--   unfold revCDerivProj; fun_trans

-- @[fun_trans]
-- theorem HSMul.hSMul.arg_a0a1.revCDerivProjUpdate_rule
--     (f : X → K) (g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
--     (revCDerivProjUpdate K Yi fun x => f x • g x)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       let zdg := revCDerivProjUpdate K Yi g x
--       (ydf.1 • zdg.1,
--        fun i (dy : YI i) dx =>
--          let dk := inner (structProj zdg.1 i) dy
--          let dy' := conj ydf.1•dy
--          let dx := zdg.2 i dy' dx
--          ydf.2 dk dx) := by
--   unfold revCDerivProjUpdate
--   fun_trans; simp[revCDerivUpdate,add_assoc,smul_pull]
--   simp only [smul_pull,revCDerivProj,revCDeriv]

-- end SMulOnSemiHilbert


-- -- HDiv.hDiv -------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- @[fun_trans]
-- theorem HDiv.hDiv.arg_a0a1.revCDeriv_rule
--     (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : ∀ x, g x ≠ 0) :
--     (revCDeriv K fun x => f x / g x)
--     =
--     fun x =>
--       let ydf := revCDeriv K f x
--       let zdg := revCDerivUpdate K g x
--       (ydf.1 / zdg.1,
--        fun dx' => (1 / (conj zdg.1)^2) • (zdg.2 (-conj ydf.1 • dx') (conj zdg.1 • ydf.2 dx'))) := by
--   unfold revCDeriv; simp
--   fun_trans (disch:=assumption)
--   simp[revCDerivUpdate,smul_push,neg_pull,revCDeriv,smul_add,smul_sub, ← sub_eq_add_neg]

-- @[fun_trans]
-- theorem HDiv.hDiv.arg_a0a1.revCDerivUpdate_rule
--     (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : ∀ x, g x ≠ 0) :
--     (revCDerivUpdate K fun x => f x / g x)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       let zdg := revCDerivUpdate K g x
--       (ydf.1 / zdg.1,
--        fun dx' dx =>
--          let c := (1 / (conj zdg.1)^2)
--          let a := -(c * conj ydf.1)
--          let b := c * conj zdg.1
--          ((zdg.2 (a • dx') (ydf.2 (b • dx') dx)))) := by
--   funext
--   simp[revCDerivUpdate]
--   fun_trans (disch:=assumption)
--   simp[revCDerivUpdate,smul_push,neg_pull,revCDeriv,smul_add,smul_sub,add_assoc,mul_assoc]


-- @[fun_trans]
-- theorem HDiv.hDiv.arg_a0a1.revCDerivProj_rule
--     (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : ∀ x, g x ≠ 0) :
--     (revCDerivProj K Unit fun x => f x / g x)
--     =
--     fun x =>
--       let ydf := revCDeriv K f x
--       let zdg := revCDerivUpdate K g x
--       (ydf.1 / zdg.1,
--        fun _ dx' => (1 / (conj zdg.1)^2) • (zdg.2 (-conj ydf.1 • dx') (conj zdg.1 • ydf.2 dx'))) :=
-- by
--   unfold revCDerivProj
--   fun_trans (disch:=assumption); simp[oneHot, structMake]

-- @[fun_trans]
-- theorem HDiv.hDiv.arg_a0a1.revCDerivProjUpdate_rule
--     (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : ∀ x, g x ≠ 0) :
--     (revCDerivProjUpdate K Unit fun x => f x / g x)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       let zdg := revCDerivUpdate K g x
--       (ydf.1 / zdg.1,
--        fun _ dx' dx =>
--          let c := (1 / (conj zdg.1)^2)
--          let a := -(c * conj ydf.1)
--          let b := c * conj zdg.1
--          ((zdg.2 (a • dx') (ydf.2 (b • dx') dx)))) :=
-- by
--   unfold revCDerivProjUpdate
--   fun_trans (disch:=assumption)
--   simp[revCDerivUpdate,revCDeriv,add_assoc,neg_pull,mul_assoc,smul_push]


-- -- HPow.hPow -------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- @[fun_trans]
-- def HPow.hPow.arg_a0.revCDeriv_rule
--     (f : X → K) (n : Nat) (hf : HasAdjDiff K f) :
--     revCDeriv K (fun x => f x ^ n)
--     =
--     fun x =>
--       let ydf := revCDeriv K f x
--       let y' := (n : K) * (conj ydf.1 ^ (n-1))
--       (ydf.1 ^ n,
--        fun dx' => ydf.2 (y' * dx')) :=
-- by
--   funext x
--   unfold revCDeriv; simp; funext dx; fun_trans; simp[smul_push,smul_smul]; ring_nf

-- @[fun_trans]
-- def HPow.hPow.arg_a0.revCDerivUpdate_rule
--     (f : X → K) (n : Nat) (hf : HasAdjDiff K f) :
--     revCDerivUpdate K (fun x => f x ^ n)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       let y' := n * (conj ydf.1 ^ (n-1))
--       (ydf.1 ^ n,
--        fun dy dx => ydf.2 (y' * dy) dx) := by
--   unfold revCDerivUpdate
--   funext x; fun_trans

-- @[fun_trans]
-- def HPow.hPow.arg_a0.revCDerivProj_rule
--     (f : X → K) (n : Nat) (hf : HasAdjDiff K f) :
--     revCDerivProj K Unit (fun x => f x ^ n)
--     =
--     fun x =>
--       let ydf := revCDeriv K f x
--       let y' := (n : K) * (conj ydf.1 ^ (n-1))
--       (ydf.1 ^ n, fun _ dx' => ydf.2 (y' * dx')) := by
--   unfold revCDerivProj; fun_trans; simp[oneHot,structMake]

-- @[fun_trans]
-- def HPow.hPow.arg_a0.revCDerivProjUpdate_rule
--     (f : X → K) (n : Nat) (hf : HasAdjDiff K f) :
--     revCDerivProjUpdate K Unit (fun x => f x ^ n)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       let y' := n * (conj ydf.1 ^ (n-1))
--       (ydf.1 ^ n,
--        fun _ dy dx => ydf.2 (y' * dy) dx) := by
--   unfold revCDerivProjUpdate; fun_trans; simp[oneHot,structMake,revCDerivUpdate]


-- -- sum ----------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- section IndexTypeSum

-- variable {ι : Type} [IndexType ι nι]

-- @[fun_trans]
-- theorem sum.arg_f.revCDeriv_rule
--   (f : X → ι → Y) (hf : ∀ i, HasAdjDiff K (fun x => f x i))
--   : revCDeriv K (fun x => ∑ i, f x i)
--     =
--     fun x =>
--       let ydf := revCDeriv K f x
--       (∑ i, ydf.1 i,
--        fun dy =>
--          ydf.2 (fun _ => dy)) :=
-- by
--   unfold revCDeriv
--   fun_trans;
--   funext x; simp; funext dy;
--   conv => rhs; rw[cderiv.pi_rule (hf := by fun_prop)];
--   fun_trans


-- @[fun_trans]
-- theorem sum.arg_f.revCDerivUpdate_rule
--     (f : X → ι → Y) (hf : ∀ i, HasAdjDiff K (fun x => f x i)) :
--     revCDerivUpdate K (fun x => ∑ i, f x i)
--     =
--     fun x =>
--       let ydf := revCDerivUpdate K f x
--       (∑ i, ydf.1 i,
--        fun dy dx =>
--          ydf.2 (fun _ => dy) dx) := by
--   unfold revCDerivUpdate
--   fun_trans

-- @[fun_trans]
-- theorem sum.arg_f.revCDerivProj_rule [DecidableEq ι]
--     (f : X → ι → Y') (hf : ∀ i, HasAdjDiff K (fun x => f x i)) :
--     revCDerivProj K Yi (fun x => ∑ i, f x i)
--     =
--     fun x =>
--       -- this is not optimal
--       -- we should have but right now there is no appropriate StrucLike instance
--       -- let ydf := revCDerivProj K Yi f x
--       let ydf := revCDerivProjUpdate K (ι×Yi) f x
--       (∑ i, ydf.1 i,
--        fun j dy =>
--          IndexType.foldl (fun dx i => ydf.2 (i,j) dy dx) 0) := by
--   unfold revCDerivProj
--   fun_trans
--   sorry_proof


-- @[fun_trans]
-- theorem sum.arg_f.revCDerivProjUpdate_rule [DecidableEq ι]
--     (f : X → ι → Y') (hf : ∀ i, HasAdjDiff K (fun x => f x i)) :
--     revCDerivProjUpdate K Yi (fun x => ∑ i, f x i)
--     =
--     fun x =>
--       let ydf := revCDerivProjUpdate K (ι×Yi) f x
--       (∑ i, ydf.1 i,
--        fun j dy dx =>
--          IndexType.foldl (fun dx i => ydf.2 (i,j) dy dx) dx) := by
--   sorry_proof


-- end IndexTypeSum


-- -- d/ite -----------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- @[fun_trans]
-- theorem ite.arg_te.revCDeriv_rule
--     (c : Prop) [dec : Decidable c] (t e : X → Y) :
--     revCDeriv K (fun x => ite c (t x) (e x))
--     =
--     fun y =>
--       ite c (revCDeriv K t y) (revCDeriv K e y) := by
--   induction dec
--   case isTrue h  => ext y <;> simp[h]
--   case isFalse h => ext y <;> simp[h]

-- @[fun_trans]
-- theorem ite.arg_te.revCDerivUpdate_rule
--     (c : Prop) [dec : Decidable c] (t e : X → Y) :
--     revCDerivUpdate K (fun x => ite c (t x) (e x))
--     =
--     fun y =>
--       ite c (revCDerivUpdate K t y) (revCDerivUpdate K e y) := by
--   induction dec
--   case isTrue h  => ext y <;> simp[h]
--   case isFalse h => ext y <;> simp[h]

-- @[fun_trans]
-- theorem ite.arg_te.revCDerivProj_rule
--     (c : Prop) [dec : Decidable c] (t e : X → Y') :
--     revCDerivProj K Yi (fun x => ite c (t x) (e x))
--     =
--     fun y =>
--       ite c (revCDerivProj K Yi t y) (revCDerivProj K Yi e y) := by
--   induction dec
--   case isTrue h  => ext y <;> simp[h]
--   case isFalse h => ext y <;> simp[h]

-- @[fun_trans]
-- theorem ite.arg_te.revCDerivProjUpdate_rule
--     (c : Prop) [dec : Decidable c] (t e : X → Y') :
--     revCDerivProjUpdate K Yi (fun x => ite c (t x) (e x))
--     =
--     fun y =>
--       ite c (revCDerivProjUpdate K Yi t y) (revCDerivProjUpdate K Yi e y) := by
--   induction dec
--   case isTrue h  => ext y <;> simp[h]
--   case isFalse h => ext y <;> simp[h]


-- @[fun_trans]
-- theorem dite.arg_te.revCDeriv_rule
--     (c : Prop) [dec : Decidable c]
--     (t : c  → X → Y) (e : ¬c → X → Y) :
--     revCDeriv K (fun x => dite c (t · x) (e · x))
--     =
--     fun y =>
--       dite c (fun p => revCDeriv K (t p) y)
--              (fun p => revCDeriv K (e p) y) := by
--   induction dec
--   case isTrue h  => ext y <;> simp[h]
--   case isFalse h => ext y <;> simp[h]

-- @[fun_trans]
-- theorem dite.arg_te.revCDerivUpdate_rule
--     (c : Prop) [dec : Decidable c]
--     (t : c  → X → Y) (e : ¬c → X → Y) :
--     revCDerivUpdate K (fun x => dite c (t · x) (e · x))
--     =
--     fun y =>
--       dite c (fun p => revCDerivUpdate K (t p) y)
--              (fun p => revCDerivUpdate K (e p) y) := by
--   induction dec
--   case isTrue h  => ext y <;> simp[h]
--   case isFalse h => ext y <;> simp[h]

-- @[fun_trans]
-- theorem dite.arg_te.revCDerivProj_rule
--     (c : Prop) [dec : Decidable c]
--     (t : c  → X → Y') (e : ¬c → X → Y') :
--     revCDerivProj K Yi (fun x => dite c (t · x) (e · x))
--     =
--     fun y =>
--       dite c (fun p => revCDerivProj K Yi (t p) y)
--              (fun p => revCDerivProj K Yi (e p) y) := by
--   induction dec
--   case isTrue h  => ext y <;> simp[h]
--   case isFalse h => ext y <;> simp[h]

-- @[fun_trans]
-- theorem dite.arg_te.revCDerivProjUpdate_rule
--     (c : Prop) [dec : Decidable c]
--     (t : c  → X → Y') (e : ¬c → X → Y') :
--     revCDerivProjUpdate K Yi (fun x => dite c (t · x) (e · x))
--     =
--     fun y =>
--       dite c (fun p => revCDerivProjUpdate K Yi (t p) y)
--              (fun p => revCDerivProjUpdate K Yi (e p) y) := by
--   induction dec
--   case isTrue h  => ext y <;> simp[h]
--   case isFalse h => ext y <;> simp[h]


-- --------------------------------------------------------------------------------

-- section InnerProductSpace

-- variable
--   {R : Type _} [RealScalar R]
--   -- {K : Type _} [Scalar R K]
--   {X : Type _} [SemiInnerProductSpace R X]
--   {Y : Type _} [SemiHilbert R Y]

-- -- Inner -----------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- open ComplexConjugate

-- @[fun_trans]
-- theorem Inner.inner.arg_a0a1.revCDeriv_rule
--     (f : X → Y) (g : X → Y) (hf : HasAdjDiff R f) (hg : HasAdjDiff R g) :
--     (revCDeriv R fun x => ⟪f x, g x⟫[R])
--     =
--     fun x =>
--       let y₁df := revCDeriv R f x
--       let y₂dg := revCDerivUpdate R g x
--       (⟪y₁df.1, y₂dg.1⟫[R],
--        fun dr =>
--          y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1))) := by
--   funext; simp[revCDeriv,revCDerivUpdate]
--   fun_trans[smul_pull]

-- @[fun_trans]
-- theorem Inner.inner.arg_a0a1.revCDerivUpdate_rule
--     (f : X → Y) (g : X → Y) (hf : HasAdjDiff R f) (hg : HasAdjDiff R g) :
--     (revCDerivUpdate R fun x => ⟪f x, g x⟫[R])
--     =
--     fun x =>
--       let y₁df := revCDerivUpdate R f x
--       let y₂dg := revCDerivUpdate R g x
--       (⟪y₁df.1, y₂dg.1⟫[R],
--        fun dr dx =>
--          y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1) dx) ) := by
--   unfold revCDerivUpdate
--   fun_trans; simp[revCDerivUpdate,add_assoc]

-- @[fun_trans]
-- theorem Inner.inner.arg_a0a1.revCDerivProj_rule
--     (f : X → Y) (g : X → Y) (hf : HasAdjDiff R f) (hg : HasAdjDiff R g) :
--     (revCDerivProj R Unit fun x => ⟪f x, g x⟫[R])
--     =
--     fun x =>
--       let y₁df := revCDeriv R f x
--       let y₂dg := revCDerivUpdate R g x
--       (⟪y₁df.1, y₂dg.1⟫[R],
--        fun _ dr =>
--          y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1))) := by
--   funext
--   simp[revCDerivProj]
--   fun_trans; simp[oneHot, structMake]

-- @[fun_trans]
-- theorem Inner.inner.arg_a0a1.revCDerivProjUpdate_rule
--     (f : X → Y) (g : X → Y) (hf : HasAdjDiff R f) (hg : HasAdjDiff R g) :
--     (revCDerivProjUpdate R Unit fun x => ⟪f x, g x⟫[R])
--     =
--     fun x =>
--       let y₁df := revCDerivUpdate R f x
--       let y₂dg := revCDerivUpdate R g x
--       (⟪y₁df.1, y₂dg.1⟫[R],
--        fun _ dr dx =>
--          y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1) dx)) := by
--   funext
--   simp[revCDerivProjUpdate]
--   fun_trans; simp[revCDerivUpdate,add_assoc]


-- -- norm2 -----------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- @[fun_trans]
-- theorem SciLean.Norm2.norm2.arg_a0.revCDeriv_rule
--     (f : X → Y) (hf : HasAdjDiff R f) :
--     (revCDeriv R fun x => ‖f x‖₂²[R])
--     =
--     fun x =>
--       let ydf := revCDeriv R f x
--       let ynorm2 := ‖ydf.1‖₂²[R]
--       (ynorm2,
--        fun dr =>
--          ((2:R) * dr) • ydf.2 ydf.1) := by
--   funext x; simp[revCDeriv]
--   fun_trans[smul_smul]

-- @[fun_trans]
-- theorem SciLean.Norm2.norm2.arg_a0.revCDerivUpdate_rule
--     (f : X → Y) (hf : HasAdjDiff R f) :
--     (revCDerivUpdate R fun x => ‖f x‖₂²[R])
--     =
--     fun x =>
--       let ydf := revCDerivUpdate R f x
--       let ynorm2 := ‖ydf.1‖₂²[R]
--       (ynorm2,
--        fun dr dx =>
--           ydf.2 (((2:R)*dr)•ydf.1) dx) := by
--   funext x; simp[revCDerivUpdate]
--   fun_trans; simp[revCDeriv,smul_pull]

-- @[fun_trans]
-- theorem SciLean.Norm2.norm2.arg_a0.revCDerivProj_rule
--     (f : X → Y) (hf : HasAdjDiff R f) :
--     (revCDerivProj R Unit fun x => ‖f x‖₂²[R])
--     =
--     fun x =>
--       let ydf := revCDeriv R f x
--       let ynorm2 := ‖ydf.1‖₂²[R]
--       (ynorm2,
--        fun _ dr =>
--          ((2:R) * dr) • ydf.2 ydf.1) := by
--   funext x; simp[revCDerivProj]
--   fun_trans; simp[oneHot,structMake]

-- @[fun_trans]
-- theorem SciLean.Norm2.norm2.arg_a0.revCDerivProjUpdate_rule
--     (f : X → Y) (hf : HasAdjDiff R f) :
--     (revCDerivProjUpdate R Unit fun x => ‖f x‖₂²[R])
--     =
--     fun x =>
--       let ydf := revCDerivUpdate R f x
--       let ynorm2 := ‖ydf.1‖₂²[R]
--       (ynorm2,
--        fun _ dr dx =>
--           ydf.2 (((2:R)*dr)•ydf.1) dx) := by
--   funext x; simp[revCDerivProjUpdate]
--   fun_trans only; simp[revCDeriv,revCDerivUpdate,smul_pull]


-- -- norm₂ -----------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- @[fun_trans]
-- theorem SciLean.norm₂.arg_x.revCDeriv_rule_at
--     (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0) :
--     (revCDeriv R (fun x => ‖f x‖₂[R]) x)
--     =
--     let ydf := revCDeriv R f x
--     let ynorm := ‖ydf.1‖₂[R]
--     (ynorm,
--      fun dr =>
--        (ynorm⁻¹ * dr) • ydf.2 ydf.1) := by
--   simp[revCDeriv]
--   fun_trans (disch:=assumption) only
--   simp[smul_smul]

-- @[fun_trans]
-- theorem SciLean.norm₂.arg_x.revCDerivUpdate_rule_at
--     (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0) :
--     (revCDerivUpdate R (fun x => ‖f x‖₂[R]) x)
--     =
--     let ydf := revCDerivUpdate R f x
--     let ynorm := ‖ydf.1‖₂[R]
--     (ynorm,
--      fun dr dx =>
--        ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx) := by
--   simp[revCDerivUpdate]
--   fun_trans (disch:=assumption) only
--   simp[revCDeriv,smul_pull]

-- @[fun_trans]
-- theorem SciLean.norm₂.arg_x.revCDerivProj_rule_at
--     (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0) :
--     (revCDerivProj R Unit (fun x => ‖f x‖₂[R]) x)
--     =
--     let ydf := revCDeriv R f x
--     let ynorm := ‖ydf.1‖₂[R]
--     (ynorm,
--      fun _ dr =>
--        (ynorm⁻¹ * dr) • ydf.2 ydf.1):= by
--   simp[revCDerivProj]
--   fun_trans (disch:=assumption) only; simp[oneHot, structMake]

-- @[fun_trans]
-- theorem SciLean.norm₂.arg_x.revCDerivProjUpdate_rule_at
--     (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0) :
--     (revCDerivProjUpdate R Unit (fun x => ‖f x‖₂[R]) x)
--     =
--     let ydf := revCDerivUpdate R f x
--     let ynorm := ‖ydf.1‖₂[R]
--     (ynorm,
--      fun _ dr dx =>
--        ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx):=
-- by
--   have ⟨_,_⟩ := hf
--   simp[revCDerivProjUpdate]
--   fun_trans (disch:=assumption) only
--   simp[revCDeriv,revCDerivUpdate,smul_pull]

-- @[fun_trans]
-- theorem SciLean.norm₂.arg_x.revCDeriv_rule
--     (f : X → Y) (hf : HasAdjDiff R f) (hx : ∀ x, f x≠0) :
--     (revCDeriv R (fun x => ‖f x‖₂[R]))
--     =
--     fun x =>
--       let ydf := revCDeriv R f x
--       let ynorm := ‖ydf.1‖₂[R]
--       (ynorm,
--        fun dr =>
--          (ynorm⁻¹ * dr) • ydf.2 ydf.1):=
-- by
--   unfold revCDeriv
--   funext x; simp
--   fun_trans (disch:=assumption)
--   simp[smul_smul]

-- @[fun_trans]
-- theorem SciLean.norm₂.arg_x.revCDerivUpdate_rule
--     (f : X → Y) (hf : HasAdjDiff R f) (hx : ∀ x, f x≠0) :
--     (revCDerivUpdate R (fun x => ‖f x‖₂[R]))
--     =
--     fun x =>
--       let ydf := revCDerivUpdate R f x
--       let ynorm := ‖ydf.1‖₂[R]
--       (ynorm,
--        fun dr dx =>
--          ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx):=
-- by
--   unfold revCDerivUpdate
--   funext x; simp
--   fun_trans (disch:=assumption) only
--   simp[revCDeriv,smul_pull]

-- @[fun_trans]
-- theorem SciLean.norm₂.arg_x.revCDerivProj_rule
--     (f : X → Y) (hf : HasAdjDiff R f) (hx : ∀ x, f x≠0) :
--     (revCDerivProj R Unit (fun x => ‖f x‖₂[R]))
--     =
--     fun x =>
--       let ydf := revCDeriv R f x
--       let ynorm := ‖ydf.1‖₂[R]
--       (ynorm,
--        fun _ dr =>
--          (ynorm⁻¹ * dr) • ydf.2 ydf.1) := by
--   unfold revCDerivProj
--   funext x; simp
--   fun_trans (disch:=assumption) only
--   simp[oneHot, structMake]

-- @[fun_trans]
-- theorem SciLean.norm₂.arg_x.revCDerivProjUpdate_rule
--     (f : X → Y) (hf : HasAdjDiff R f) (hx : ∀ x, f x≠0) :
--     (revCDerivProjUpdate R Unit (fun x => ‖f x‖₂[R]))
--     =
--     fun x =>
--        let ydf := revCDerivUpdate R f x
--        let ynorm := ‖ydf.1‖₂[R]
--        (ynorm,
--         fun _ dr dx =>
--           ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx) := by
--   unfold revCDerivProjUpdate
--   funext x; simp
--   fun_trans (disch:=assumption) only
--   simp[revCDeriv,revCDerivUpdate,smul_pull]

-- end InnerProductSpace
