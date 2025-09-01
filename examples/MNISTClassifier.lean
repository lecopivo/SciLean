 import Lean
-- import SciLean
import SciLean.Data.ArrayType.Algebra
import SciLean.Data.DataArray
import SciLean.Core.FloatAsReal
import SciLean.Data.Random

import SciLean.Modules.ML.Dense
import SciLean.Modules.ML.Convolution
import SciLean.Modules.ML.Pool
import SciLean.Modules.ML.MNIST

import SciLean.Util.Profile


open SciLean
open IO FS System

@[noinline] def blackbox : α → IO α := pure

def checkFileExists (path : FilePath) : IO Unit := do
  
  if ¬(← path.pathExists) then
     throw (IO.userError s!"MNIST data file '{path}' not found. Please download binary version from https://git-disl.github.io/GTDLBench/datasets/mnist_datasets/ and extract it in 'data' directory")

def toFloatRepr (b : ByteArray) (ι : Type _) [Index ι] (_ : b.size = sizeOf ι) : Float^ι :=
  ⊞ i => 
    let val := b.uget (toIdx i).1 sorry_proof
    val.toUSize.toFloat / 256.0

open IO FS System in
def loadImages (path : FilePath) (maxImages : Nat) : IO (Array (Float^[28,28])) := do 
  
  checkFileExists path

  if maxImages = 0 then 
    return #[]

  let start ← IO.monoMsNow
  IO.print s!"loading images from {path} ... "
  let data ← 
    IO.FS.withFile path .read fun m => do
      let _header ← m.read 16 -- discart 16 byte header
      let mut data : Array ByteArray := #[]
      for _ in [0:maxImages] do
        let n : Nat := 28
        let nums ← m.read (n*n).toUSize
        if nums.size = 0 then
          break
        data := data.push nums
      pure data

  if data.size ≠ maxImages then
    throw <| IO.userError s!"file {path} contains only {data.size} images"

  IO.println s!"loaded in {(← IO.monoMsNow) - start}ms"

  let start ← IO.monoMsNow
  IO.print "converting to float format ... "
  let data := data.map (toFloatRepr · (Idx 28 × Idx 28) sorry_proof)
  IO.println s!"converted in {(← IO.monoMsNow) - start}ms"

  return data


def loadLabels (path : FilePath) (maxLabels : Nat) : IO (Array (Float^[10])) := do 
  checkFileExists path

  if maxLabels = 0 then 
    return #[]

  let start ← IO.monoMsNow
  IO.print s!"loading labels from {path} ... "
  let data ← IO.FS.withFile path .read fun m => do 
    let _header ← m.read 8 -- discart 8 byte header
    m.read maxLabels.toUSize
  if data.size ≠ maxLabels then
    throw <| IO.userError s!"file {path} contains only {data.size} labels"
  IO.println s!"loaded in {(← IO.monoMsNow) - start}ms"

  let start ← IO.monoMsNow
  IO.print "converting to float format ... "
  let mut labels : Array (Float^[10]) := .mkEmpty data.size
  for b in data do
    let i : Idx 10 := ⟨b.toUSize, sorry_proof⟩
    labels := labels.push (oneHot i 1)
  IO.println s!"converted in {(← IO.monoMsNow) - start}ms"

  return labels
  

def printDigit (digit : Float^[28,28]) : IO Unit := do

  for i in fullRange (Idx 28) do
    IO.print "|"
    for j in fullRange (Idx 28) do
      let val := digit[(i,j)]
      if (val > 0.8) then
        IO.print "#"
      else if (val > 0.6) then
        IO.print "$"
      else if (val > 0.4) then
        IO.print "o"
      else if (val > 0.1) then
        IO.print "."
      else
        IO.print " "

    IO.println "|"


def prependDim (x : Float^[28,28]) : Float^[1,28,28] := ⟨x.1,sorry_proof⟩

def getBatch (i : Nat) (batchSize : USize) (images : Array (Float^[28,28])) (labels : Array (Float^[10])) 
  : Float^[1,28,28]^[batchSize] × Float^[10]^[batchSize] := Id.run do

  let mut x : Float^[1,28,28]^[batchSize] := 0
  let mut y : Float^[10]^[batchSize] := 0
  for j in fullRange (Idx batchSize) do
    let idx := i*batchSize.toNat + j.1.toNat
    x[j] := prependDim images[idx]!
    y[j] := labels[idx]!

  return (x,y)


def _root_.IO.getRand (α : Type) [Random α] : BaseIO α := Random.rand α |> IO.runRand


def main : IO Unit := do

  let trainNum := 100
  let trainImages ← loadImages "data/train-images.idx3-ubyte" trainNum
  let trainLabels ← loadLabels "data/train-labels.idx1-ubyte" trainNum

  let testNum := 0
  let testImages ← loadImages "data/t10k-images.idx3-ubyte" testNum
  let testLabels ← loadLabels "data/t10k-labels.idx1-ubyte" testNum

  IO.println ""
  
  IO.println s!"label: {trainLabels[2]!}"
  IO.println "+----------------------------+"
  printDigit trainImages[2]!
  IO.println "+----------------------------+"


  -- let start ← IO.monoMsNow
  -- IO.print "generating initial random weights ... "
  -- let w ← ML.mnist.initWeights
  -- IO.println s!"took {(← IO.monoMsNow) - start}ms"

  let (images,labels) := getBatch 0 5 trainImages trainLabels
  
  -- let start ← IO.monoMsNow
  -- IO.print "evaluating network ... "
  -- let l := ML.mnist w (← blackbox images[1])
  -- IO.println s!"took {(← IO.monoMsNow) - start}ms"
  -- IO.println l


  -- let l := images[1]
  --   |> ML.conv2d 8 1 w.1.1 w.1.2 
  --   |> ArrayType.map ML.gelu
  --   |> ML.avgPool 
  --   |> ML.dense 30 w.2.1.1 w.2.1.2
  --   |> ArrayType.map ML.gelu
  --   |> ML.dense 10 w.2.2.1 w.2.2.2

  -- IO.println l


  -- let start ← IO.monoMsNow
  -- IO.print "evaluating network gradient... "
  -- let dw := (ML.mnist.arg_wx.revDeriv w (← blackbox images[0])).2 (← IO.getRand _)
  -- IO.println s!"took {(← IO.monoMsNow) - start}ms"
  -- IO.println dw.1.2.2.2



  let start ← IO.monoMsNow
  IO.print "evaluating conv2d gradient... "
  let dweightsbiasx := (ML.conv2d.arg_weightsbiasx.revDeriv 2 1 (← IO.getRand _) (← IO.getRand _) images[0]).2 (← IO.getRand _)
  IO.println s!"took {(← IO.monoMsNow) - start}ms"
  IO.println dweightsbiasx.1


  let start ← IO.monoMsNow
  IO.print "evaluating avgPool gradient... "
  let dimg := (ML.avgPool.arg_x.revDeriv images[0]).2 (← IO.getRand _)
  IO.println s!"took {(← IO.monoMsNow) - start}ms"
  IO.println dimg[0]


  let start ← IO.monoMsNow
  IO.print "evaluating map gelu gradient... "
  let dimg := ((revDeriv Float (fun x => ArrayType.map ML.gelu x) images[0]).2 (← IO.getRand _)) rewrite_by ftrans
  IO.println s!"took {(← IO.monoMsNow) - start}ms"
  IO.println dimg[0]


  let start ← IO.monoMsNow
  IO.print "evaluating dense gradient... "
  let dimg :=  (ML.dense.arg_weightsbiasx.revDeriv 10 (← IO.getRand _) (← IO.getRand _) labels[0]).2 (← IO.getRand _)  
  IO.println s!"took {(← IO.monoMsNow) - start}ms"
  IO.println dimg.1
  


