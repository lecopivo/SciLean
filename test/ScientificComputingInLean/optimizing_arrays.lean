import SciLean
import SciLean.Util.DefOptimize
import SciLean.Tactic.OptimizeIndexAccess

open SciLean


theorem mapMono_mapMono {I} [IndexType I] (x : Float^[I]) (f g : Float → Float) :
    (x.mapMono f |>.mapMono g) = x.mapMono fun x => g (f x) := sorry_proof

theorem mapIdxMono_mapMono {I} [IndexType I] (x : Float^[I]) (f : I → Float → Float) (g : Float → Float) :
    (x.mapIdxMono f |>.mapMono g) = x.mapIdxMono fun i x => g (f i x) := sorry_proof

theorem mapMono_mapIdxMono {I} [IndexType I] (x : Float^[I]) (f : Float → Float) (g : I → Float → Float) :
    (x.mapMono f |>.mapIdxMono g) = x.mapIdxMono fun i x => (g i (f x)) := sorry_proof

theorem mapIdxMono_mapIdxMono {I} [IndexType I] (x : Float^[I]) (f g : I → Float → Float) :
    (x.mapIdxMono f |>.mapIdxMono g) = x.mapIdxMono fun i x => g i (f i x) := sorry_proof


def saxpy {n} (a : Float) (x y : Float^[n]) := (a•x+y)
  rewrite_by
    simp only [HAdd.hAdd,Add.add,HSMul.hSMul,SMul.smul]
    simp only [mapMono_mapIdxMono]


def saxpy_naive {n} (a : Float) (x y : Float^[n]) := (a•x+y)

def_optimize saxpy_naive by
  simp only [HAdd.hAdd,Add.add,HSMul.hSMul,SMul.smul]
  simp only [mapMono_mapIdxMono]


/--
info: saxpy_naive.optimized {n : ℕ} (a : Float) (x y : DataArrayN Float (Fin n)) : DataArrayN Float (Fin n)
-/
#guard_msgs in
#check saxpy_naive.optimized

/--
info: saxpy_naive.optimize_rule {n : ℕ} (a : Float) (x y : DataArrayN Float (Fin n)) :
  saxpy_naive a x y = saxpy_naive.optimized a x y
-/
#guard_msgs in
#check saxpy_naive.optimize_rule




def matVecMul {n m} (A : Float^[n,m]) (x : Float^[m]) := ⊞ i => ∑ j, A[i,j] * x[j]

def_optimize matVecMul by
  simp only [LeanColls.IndexType.toFin_prod]
  simp only [GetElem.getElem, LeanColls.GetElem'.get, DataArrayN.get, IndexType.toFin, id,
             Fin.pair, IndexType.fromFin, Fin.cast, IndexType.card]


def matVecMul' {n m} (A : Float^[n,m]) (x : Float^[m]) := ⊞ i => ∑ j, A[i,j] * x[j]

def_optimize matVecMul' by optimize_index_access


def matDot {n m} (A B : Float^[n,m]) := ∑ (ij : Fin n × Fin m), A[ij] * B[ij]

open LeanColls IndexType in
-- this option will display the type of the index we are summing over
set_option pp.funBinderTypes true in
def_optimize matDot by
  -- rewrite `sum` over `Fin n × Fin m` to `fold` over `Fin (n*m)`
  rw[sum_linearize]

  -- unfold several layers of abstraction for `get` function
  simp only [GetElem.getElem, LeanColls.GetElem'.get, DataArrayN.get]

  -- simplify `toFin (fromFin i)` to `i`
  simp only [toFin_fromFin]

  -- clean up some expressions
  simp only [Fin.cast,IndexType.card]


def matDot' {n m} (A B : Float^[n,m]) := ∑ (ij : Fin n × Fin m), A[ij] * B[ij]

set_option pp.funBinderTypes true in
def_optimize matDot' by optimize_index_access
