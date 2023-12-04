 import Lean
-- import SciLean
import SciLean.Data.DataArray
import SciLean.Core.FloatAsReal

open SciLean
open IO FS System

def checkFileExists (path : FilePath) : IO Unit := do
  
  if ¬(← path.pathExists) then
     throw (IO.userError s!"MNIST data file '{path}' not found. Please download binary version from https://git-disl.github.io/GTDLBench/datasets/mnist_datasets/ and extract it in 'data' directory")

def toFloatRepr (b : ByteArray) (ι : Type _) [Index ι] (_ : b.size = sizeOf ι) : Float^ι := Id.run do  
  let mut idx : USize := 0
  let mut x : Float^ι := 0
  for i in fullRange ι do
    let val := b.uget idx sorry_proof
    x[i] := val.toNat.toFloat / 256.0
    idx := idx + 1
  x

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


