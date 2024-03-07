import SciLean.Core.Objects.BroadcastType

import Mathlib.Tactic.FunTrans.Attr
import Mathlib.Tactic.FunTrans.Elab

namespace SciLean



-- todo: maybe rename to `vectorize`, also find synergy with `StructType` maybe they differe only in outParams
/--
Broadcast vectorizes operations. For example, broadcasting multiplication `fun (x : ℝ) => c * x` will produce scalar multiplication `fun (x₁,...,xₙ) => (c*x₁,...,c*x₂)`.

Arguments

1. `tag` - type of broadcasting. The most versatile is `Prod` but dense and sparse matrices are planed in the future.
2. `R`   - field/ring over which we do broadcasting. This is usually ℝ or ℂ. Right now, it is not clear what is the role of this argument for broadcasting, but we need it to specify
3. `ι`   - broadcast to `ι`-many copies. For example, with `ι := Fin 2` broadcasting `ℝ → ℝ` will produce `ℝ×ℝ → ℝ×ℝ`(for `tag:=Prod`) or `NArray ℝ 2 → NArray ℝ 2`(for `tag := NArray`, currently not supported)

-/
@[fun_trans]
def broadcast (tag : Lean.Name) (R : Type _) (ι : Type _) [Ring R]
  {X : Type _} [AddCommGroup X] [Module R X]
  {Y : Type _} [AddCommGroup Y] [Module R Y]
  {MX : Type _} [AddCommGroup MX] [Module R MX]
  {MY : Type _} [AddCommGroup MY] [Module R MY]
  [BroadcastType tag R ι X MX] [BroadcastType tag R ι Y MY]
  (f : X → Y) : MX → MY := fun mx =>
  (BroadcastType.equiv tag (R:=R)).symm fun (i : ι) => f ((BroadcastType.equiv tag (R:=R)) mx i)

def broadcastProj (tag : Lean.Name) (R : Type _) [Ring R]
  {X : Type _} [AddCommGroup X] [Module R X]
  {MX : Type _} [AddCommGroup MX] [Module R MX]
  {ι : Type _} [BroadcastType tag R ι X MX]
  (mx : MX) (i : ι) : X := (BroadcastType.equiv tag (R:=R)) mx i

def broadcastIntro (tag : Lean.Name) (R : Type _) [Ring R]
  {X : Type _} [AddCommGroup X] [Module R X]
  {MX : Type _} [AddCommGroup MX] [Module R MX]
  {ι : Type _} [BroadcastType tag R ι X MX]
  (f : ι → X) : MX := (BroadcastType.equiv tag (R:=R)).symm f


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

section Rules

variable
  {tag : Lean.Name}
  {R : Type _} [Ring R]
  {ι : Type _}
  {X : Type _} [AddCommGroup X] [Module R X]
  {Y : Type _} [AddCommGroup Y] [Module R Y]
  {Z : Type _} [AddCommGroup Z] [Module R Z]
  {MX : Type _} [AddCommGroup MX] [Module R MX] [BroadcastType tag R ι X MX]
  {MY : Type _} [AddCommGroup MY] [Module R MY] [BroadcastType tag R ι Y MY]
  {MZ : Type _} [AddCommGroup MZ] [Module R MZ] [BroadcastType tag R ι Z MZ]
  {κ : Type _} -- [Fintype κ]
  {E ME : κ → Type _}
  [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
  [∀ j, AddCommGroup (ME j)] [∀ j, Module R (ME j)]
  [∀ j, BroadcastType tag R ι (E j) (ME j)]


@[fun_trans]
theorem id_rule
  : broadcast tag R ι (fun (x : X) => x)
    =
    fun (mx : MX) => mx :=
by
  unfold broadcast
  simp

@[fun_trans]
theorem const_rule (y : Y)
  : broadcast tag R ι (fun (_ : X) => y)
    =
    fun (_ : MX) => broadcastIntro tag R (fun (_ : ι) => y) :=
by
  unfold broadcast
  simp [broadcastIntro]


@[fun_trans]
theorem comp_rule
  (g : X → Y) (f : Y → Z)
  : broadcast tag R ι (fun x => f (g x))
    =
    fun mx => broadcast tag R ι f (broadcast tag R ι g mx) :=
by
  unfold broadcast
  simp[broadcast]

@[fun_trans]
theorem let_rule
  (g : X → Y) (f : X → Y → Z)
  : broadcast tag R ι (fun x => let y := g x; f x y)
    =
    fun mx =>
      let my := broadcast tag R ι g mx
      let mz := broadcast tag R ι (fun (xy : X×Y) => f xy.1 xy.2) (mx,my)
      mz :=
by
  rw[show (fun x => let y := g x; f x y)
          =
          fun x => (fun (xy : X×Y) => f xy.1 xy.2) ((fun x' => (x', g x')) x) by rfl]
  rw[comp_rule _ _]
  funext mx; simp[broadcast, BroadcastType.equiv]

@[fun_trans]
theorem apply_rule (j : κ)
  : broadcast tag R ι (fun (x : (j : κ) → E j) => x j)
    =
    fun (mx : (j : κ ) → ME j) => mx j :=
by
  unfold broadcast
  simp[broadcastIntro, BroadcastType.equiv]

@[fun_trans]
theorem pi_rule
  (f : X → (j : κ) → E j)
  : broadcast tag R ι (fun x j => f x j)
    =
    fun mx j => (broadcast tag R ι (f · j) mx) :=
by
  funext mx j
  simp[broadcast,BroadcastType.equiv]


end Rules

end SciLean

section Functions

open SciLean

variable
  {R : Type _} [Ring R]
  {X : Type _} [AddCommGroup X] [Module R X]
  {Y : Type _} [AddCommGroup Y] [Module R Y]
  {Z : Type _} [AddCommGroup Z] [Module R Z]
  {ι : Type _} {tag : Lean.Name}
  {MR : Type _} [AddCommGroup MR] [Module R MR] [BroadcastType tag R ι R MR]
  {MX : Type _} [AddCommGroup MX] [Module R MX] [BroadcastType tag R ι X MX]
  {MY : Type _} [AddCommGroup MY] [Module R MY] [BroadcastType tag R ι Y MY]
  {MZ : Type _} [AddCommGroup MZ] [Module R MZ] [BroadcastType tag R ι Z MZ]
  {κ : Type _} -- [Fintype κ]
  {E ME : κ → Type _}
  [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
  [∀ j, AddCommGroup (ME j)] [∀ j, Module R (ME j)]
  [∀ j, BroadcastType tag R ι (E j) (ME j)]


-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_trans]
theorem Prod.mk.arg_fstsnd.broadcast_rule
  (g : X → Y)
  (f : X → Z)
  : broadcast tag R ι (fun x => (g x, f x))
    =
    fun (mx : MX) => (broadcast tag R ι g mx,
                      broadcast tag R ι f mx) :=
by
  funext mx; simp[broadcast, BroadcastType.equiv]


@[fun_trans]
theorem Prod.fst.arg_self.broadcast_rule
  (f : X → Y×Z)
  : broadcast tag R ι (fun x => (f x).1)
    =
    fun mx => (broadcast tag R ι f mx).1 :=
by
  funext mx; simp[broadcast, BroadcastType.equiv]


@[fun_trans]
theorem Prod.snd.arg_self.broadcast_rule
  (f : X → Y×Z)
  : broadcast tag R ι (fun x => (f x).2)
    =
    fun mx => (broadcast tag R ι f mx).2 :=
by
  funext mx; simp[broadcast, BroadcastType.equiv]



-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.broadcast_rule (f g : X → Y)
  : (broadcast tag R ι fun x => f x + g x)
    =
    fun mx =>
      broadcast tag R ι f mx + broadcast tag R ι g mx :=
by
  funext mx; unfold broadcast; rw[← map_add]; rfl



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSub.hSub.arg_a0a1.broadcast_rule (f g : X → Y)
  : (broadcast tag R ι fun x => f x - g x)
    =
    fun mx =>
      broadcast tag R ι f mx - broadcast tag R ι g mx :=
by
  funext mx; unfold broadcast; rw[← map_sub]; rfl



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Neg.neg.arg_a0.broadcast_rule (f : X → Y)
  : (broadcast tag R ι fun x => - f x)
    =
    fun mx => - broadcast tag R ι f mx :=
by
  funext mx; unfold broadcast; rw[← map_neg]; rfl



-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HMul.hMul.arg_a1.broadcast_rule
  (f : R → R) (c : R)
  : (broadcast tag R ι fun x => c * f x)
    =
    fun mx => c • (broadcast tag R ι f mx) :=
by
  funext mx; unfold broadcast; rw[← map_smul]; rfl


@[fun_trans]
theorem HMul.hMul.arg_a0.broadcast_rule
  {R : Type _} [CommRing R]
  {ι : Type _} {tag : Lean.Name}
  {MR : Type _} [AddCommGroup MR] [Module R MR] [BroadcastType tag R ι R MR]
  (f : R → R) (c : R)
  : (broadcast tag R ι fun x => f x * c)
    =
    fun mx => c • (broadcast tag R ι f mx)  :=
by
  funext mx; unfold broadcast; rw[← map_smul]; congr; funext i; simp[mul_comm]



-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSMul.hSMul.arg_a1.broadcast_rule
  (c : R) (f : X → Y)
  : (broadcast tag R ι fun x => c • f x)
    =
    fun mx => c • broadcast tag R ι f mx :=
by
  funext mx; unfold broadcast; rw[← map_smul]; rfl


-- This has to be done for each `tag` reparatelly as we do not have access to elemntwise operations
@[fun_trans]
theorem HSMul.hSMul.arg_a0.broadcast_rule
  (f : X → R) (y : Y)
  [BroadcastType `Prod R (Fin n) X MX]
  [BroadcastType `Prod R (Fin n) Y MY]
  : (broadcast `Prod R (Fin (n+1)) fun x => f x • y)
    =
    fun (x,mx) => (f x • y, (broadcast `Prod R (Fin n) fun x => f x • y) mx) :=
by
  funext mx; unfold broadcast; rfl



end Functions
