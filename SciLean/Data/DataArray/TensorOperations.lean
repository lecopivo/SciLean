import SciLean.Data.DataArray.DataArray
import SciLean.Data.DataArray.RnEquiv
import SciLean.Data.DataArray.Algebra
import SciLean.Data.DataArray.Float
import SciLean.Data.DataArray.FloatN
import SciLean.Data.DataArray.Operations
import SciLean.Meta.Notation.Let'
import SciLean.Data.ArrayOperations.Operations

import SciLean.Analysis.Scalar.FloatAsReal

namespace SciLean.DataArrayN

variable
  {R : Type*} [RealScalar R] [pd : PlainDataType R] [BLAS (DataArray R) R R]
  {I nI} [IndexType I nI] [Fold I]
  {J nJ} [IndexType J nJ] [Fold J]
  {K nK} [IndexType K nK] [Fold K]
  {L nL} [IndexType L nL] [Fold L]
  {M nM} [IndexType M nM] [Fold M]


----------------------------------------------------------------------------------------------------
-- Operations on rows and columns for arrays of reals ----------------------------------------------
----------------------------------------------------------------------------------------------------

/--
Sum over middle dimension `J` of rank-3 tensor `R^[I,J,K]`

TODO: Maybe implement this with BLAS or something if too slow
-/
def sumMiddleR (x : R^[I,J,K]) : R^[I,K] := Id.run do
  let mut y : R^[I,K] := 0
  for i in fullRange I do
    for j in fullRange J do
      for k in fullRange K do
        y[i,k] += x[i,j,k]
  return y
  -- ⊞ (i : Idx nI) (k : Idx nK) => ∑ᴵ (j : Idx nJ),
  --   x.rget ((toIdx (i,j,k)).cast (by simp))
  -- |>.reshape (I×K) (by rfl)


variable (I) in
def replicateRowR (r : R^[J]) : R^[I,J] :=
  let data : DataArray R := DataArray.emptyWithCapacity (nI*nJ)
  ⟨data.pushArray r.1 nI, sorry_proof⟩


variable (J) in
def replicateColR (r : R^[I]) : R^[I,J] := Id.run do
  let mut data : DataArray R := DataArray.emptyWithCapacity (nI*nJ)
  for i in fullRange I do
    data := data.push r[i] nJ
  ⟨data, sorry_proof⟩

variable (J) in
def replicateMiddleR (x : R^[I,K]) : R^[I,J,K] := Id.run do
  let mut data : DataArray R := DataArray.emptyWithCapacity (nI*nJ*nK)
  for i in fullRange I do
    -- TODO: fix this! it is slow! we make copies of `x`'s rows
    data := data.pushArray (x.curry[i]).1 nJ
  ⟨data, sorry_proof⟩

/--
Add `y : R^[J]` scaled by `a : R` to `x : R^[I,J,K]` at `(i,:,k)`
-/
def scalAddMiddleR (x : R^[I,J,K]) (i : I) (k : K) (a : R) (y : R^[J]) : R^[I,J,K] := Id.run do
  let mut x := x
  for j in fullRange J do
    x[(i,j,k)] += a • y[j]
  x


def scalAddMiddle2R (x : R^[I,J,K,L,M]) (i : I) (k : K) (m : M) (a : R) (y : R^[J,L]) : R^[I,J,K,L,M] := Id.run do
  let mut x := x
  for j in fullRange J do
    for l in fullRange L do
      x[i,j,k,l,m] += a • y[j,l]
  x


def scalAddMiddleAllR (x : R^[I,J,K]) (a : R) (y : R^[J]) : R^[I,J,K] := Id.run do
  let mut x := x
  for i in fullRange I do
    for j in fullRange J do
      for k in fullRange K do
        x[(i,j,k)] += a • y[j]
  x


def scalAddMiddle2AllR (x : R^[I,J,K,L,M]) (a : R) (y : R^[J,L]) : R^[I,J,K,L,M] := Id.run do
  let mut x := x
  for i in fullRange I do
    for j in fullRange J do
      for k in fullRange K do
        for l in fullRange L do
          for m in fullRange M do
            x[i,j,k,l,m] += a • y[j,l]
  x

abbrev scalAddFstLastR (x : R^[I,J,K]) (a : R) (y : R^[I,K]) : R^[I,J,K] :=
  x |>.reshape (Unit×I×J×K×Unit) (by ac_rfl)
    |>.scalAddMiddle2AllR a y
    |>.reshape (I×J×K) (by ac_rfl)

/--
vector-matrix multiplication

TODO: call BLAS
-/
def contractLeftAddR (a : R) (x : R^[I]) (y : R^[I,J]) (b : R) (z : R^[J]) : R^[J] := Id.run do
  let mut z := z
  for i in fullRange I do
    for j in fullRange J do
      z[j] := b * z[j] + a * x[i] * y[i,j]
  z

/--
matrix-vector multiplication

TODO: call BLAS
-/
def contractRightAddR (a : R) (x : R^[I,J]) (y : R^[J]) (b : R) (z : R^[I]) : R^[I] := Id.run do
  let mut z := z
  for i in fullRange I do
    for j in fullRange J do
      z[i] := b * z[i] + a * x[i,j] * y[j]
  z

/--
Matrix-matrix multiplication

TODO: call BLAS
-/
def contractMiddleAddR (a : R) (x : R^[I,J]) (y : R^[J,K]) (b : R) (z : R^[I,K]) : R^[I,K] := Id.run do
  let mut z := z
  for i in fullRange I do
    for j in fullRange J do
      for k in fullRange K do
        z[i,k] := b * z[i,k] + a * x[i,j] * y[j,k]
  z


/--
Outer product of two vectors

TODO: call BLAS
-/
def outerAddR (a : R) (x : R^[I]) (y : R^[J]) (z : R^[I,J]) : R^[I,J] := Id.run do
  let mut z := z
  for i in fullRange I do
    for j in fullRange J do
      z[i,j] += a * x[i] * y[j]
  z


----------------------------------------------------------------------------------------------------
-- Operations on rows and columns for arrays  ------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable
  {ι nι} [IndexType ι nι] [Fold ι]
  {X : Type*} [PlainDataType X] [HasRnEquiv X ι R]


def sum (x : X^[I]) : X :=
  x |> toRn
    |>.reshape (Unit×I×ι) (by ac_rfl)
    |>.sumMiddleR
    |>.reshape (ι) (by ac_rfl)
    |> fromRn

def rsum (x : X^[I]) : R :=
  x |> toRn |>.sum

def sumCols (x : X^[I,J]) : X^[J] :=
  x |> toRn
    |>.reshape (Unit×I×(J×ι)) (by ac_rfl)
    |>.sumMiddleR
    |>.reshape (J×ι) (by ac_rfl)
    |> fromRn

def sumRows (x : X^[I,J]) : X^[I] :=
  x |> toRn
    |>.reshape (I×J×ι) (by ac_rfl)
    |>.sumMiddleR
    |> fromRn

def sumMiddle (x : X^[I,J,K]) : X^[I,K] :=
  x |> toRn
    |>.reshape (I×J×(K×ι)) (by ac_rfl)
    |>.sumMiddleR
    |>.reshape ((I×K)×ι) (by ac_rfl)
    |> fromRn

variable (I) in
def replicate (x : X) : X^[I] :=
  ⟨.replicate nI x, sorry_proof⟩

variable (I) in
def replicateRow (r : X^[J]) : X^[I,J] :=
  r |> toRn
    |>.replicateRowR I
    |>.reshape ((I×J)×ι) (by ac_rfl)
    |> fromRn

variable (J) in
def replicateCol (c : X^[I]) : X^[I,J] :=
  c |> toRn
    |>.replicateColR J
    |>.reshape ((I×J)×ι) (by ac_rfl)
    |> fromRn

def scalAdd (x : X^[I]) (a : R) (r : X) : X^[I] :=
  x |> toRn
    |>.reshape (I×ι×Unit) (by ac_rfl)
    |>.scalAddMiddleAllR a (toRn r)
    |>.reshape (I×ι) (by ac_rfl)
    |> fromRn

def scalAddRow (x : X^[I,J]) (i : I) (a : R) (r : X^[J]) : X^[I,J] :=
  x |> toRn
    |>.reshape (I×(J×ι)×Unit) (by ac_rfl)
    |>.scalAddMiddleR i () a (toRn r)
    |>.reshape ((I×J)×ι) (by ac_rfl)
    |> fromRn

abbrev addRow (x : X^[I,J]) (i : I) (r : X^[J]) : X^[I,J] := x.scalAddRow i 1 r

def scalAddRows (x : X^[I,J]) (a : R) (r : X^[J]) : X^[I,J] :=
  x |> toRn
    |>.reshape (I×(J×ι)×Unit) (by ac_rfl)
    |>.scalAddMiddleAllR a (toRn r)
    |>.reshape ((I×J)×ι) (by ac_rfl)
    |> fromRn

abbrev addRows (x : X^[I,J]) (r : X^[J]) : X^[I,J] := x.scalAddRows 1 r

def scalAddCol (x : X^[I,J]) (j : J) (a : R) (r : X^[I]) : X^[I,J] :=
  x |> toRn
    |>.reshape (Unit×I×J×ι×Unit) (by ac_rfl)
    |>.scalAddMiddle2R () j () a (toRn r)
    |>.reshape ((I×J)×ι) (by ac_rfl)
    |> fromRn

def scalAddCols (x : X^[I,J]) (a : R) (r : X^[I]) : X^[I,J] :=
  x |> toRn
    |>.reshape (Unit×I×J×ι×Unit) (by ac_rfl)
    |>.scalAddMiddle2AllR a (toRn r)
    |>.reshape ((I×J)×ι) (by ac_rfl)
    |> fromRn

abbrev addCols (x : X^[I,J]) (r : X^[I]) : X^[I,J] := x.scalAddCols 1 r



----------------------------------------------------------------------------------------------------
-- Max and min  ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


abbrev rmax (x : X^[I]) : R :=
  -- TODO: add Scalar.ninf
  have : Bot R := ⟨(-1:R)/(0:R)⟩
  let x := toRn x
  IndexType.max (fun i => x[i])


abbrev rmin (x : X^[I]) : R :=
  -- TODO: add Scalar.inf
  have : Top R := ⟨(1:R)/(0:R)⟩
  let x := toRn x
  IndexType.min (fun i => x[i])




----------------------------------------------------------------------------------------------------
-- Logsumexp and Softmax  --------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open Scalar in
def logsumexp (x : X^[I]) : R :=
  let x := toRn x
  let m := x.rmax
  log (∑ᴵ i, exp (x[i] - m)) + m

-- ugh universes require additional `Fold` :/
open Scalar in
def softmax [Fold ι] [Fold I] (x : X^[I]) : X^[I] :=
  let x := toRn x
  let m := x.rmax
  let w := ∑ᴵ i, exp (x[i] - m)
  let x := x.rmap (fun xi => w⁻¹ * exp (xi - m))
  fromRn x

open Scalar in
def logsumexpSoftmax [Fold ι] [Fold I] (x : X^[I]) : (R × X^[I]) :=
  let x := toRn x
  let m := x.rmax
  let w := ∑ᴵ i, exp (x[i] - m)
  let x := x.rmap (fun xi => w⁻¹ * exp (xi - m))
  (log w + m, fromRn x)
