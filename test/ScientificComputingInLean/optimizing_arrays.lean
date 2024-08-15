import SciLean
-- import SciLean.Util.DefOptimize
-- import SciLean.Tactic.OptimizeIndexAccess

open SciLean

variable {I : Type} [IndexType I]

theorem mapMono_mapMono (x : Float^[I]) (f g : Float → Float) :
    (x.mapMono f |>.mapMono g) = x.mapMono fun x => g (f x) := sorry_proof

theorem mapIdxMono_mapMono (x : Float^[I]) (f : I → Float → Float) (g : Float → Float) :
    (x.mapIdxMono f |>.mapMono g) = x.mapIdxMono fun i x => g (f i x) := sorry_proof

theorem mapMono_mapIdxMono (x : Float^[I]) (f : Float → Float) (g : I → Float → Float) :
    (x.mapMono f |>.mapIdxMono g) = x.mapIdxMono fun i x => (g i (f x)) := sorry_proof

theorem mapIdxMono_mapIdxMono (x : Float^[I]) (f g : I → Float → Float) :
    (x.mapIdxMono f |>.mapIdxMono g) = x.mapIdxMono fun i x => g i (f i x) := sorry_proof


def saxpy {n} (a : Float) (x y : Float^[n]) := (a•x+y)

def_optimize saxpy by
  simp only [HAdd.hAdd,Add.add,HSMul.hSMul,SMul.smul]
  simp only [mapMono_mapIdxMono]


#check saxpy.optimized

#check saxpy.optimize_rule




def matVecMul {n m} (A : Float^[n,m]) (x : Float^[m]) := ⊞ i => ∑ j, A[i,j] * x[j]

def_optimize matVecMul by
  simp only [GetElem.getElem, ArrayType.get, DataArrayN.get, IndexType.toFin, id,
             IndexType.fromFin, Fin.cast, Size.size]


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
  simp only [GetElem.getElem, ArrayType.get, DataArrayN.get]

  -- simplify `toFin (fromFin i)` to `i`
  simp only [toFin_fromFin]

  -- clean up some expressions
  simp only [Fin.cast,Size.size]


def matDot' {n m} (A B : Float^[n,m]) := ∑ (ij : Fin n × Fin m), A[ij] * B[ij]

set_option pp.funBinderTypes true in
def_optimize matDot' by optimize_index_access
