import Lean
import SciLean

open SciLean


open IO FS System

def checkFileExists (path : FilePath) : IO Unit := do
  if ¬(← path.pathExists) then
     throw (IO.userError s!"MNIST data file '{path}' not found. Please download binary version from https://git-disl.github.io/GTDLBench/datasets/mnist_datasets/ and extract it in 'data' directory")

open IO FS System in
def loadData : IO (Array ByteArray) := do 

  let trainImages : FilePath := "data/train-images.idx3-ubyte"
  let trainLabels : FilePath := "data/train-labels.idx1-ubyte"
  let testImages : FilePath :=  "data/t10k-images.idx3-ubyte"
  let testLabels : FilePath :=  "data/t10k-labels.idx1-ubyte"

  checkFileExists trainImages
  checkFileExists trainLabels
  checkFileExists testImages
  checkFileExists testLabels

  IO.FS.withFile trainImages .read fun m => do

    let mut data : Array ByteArray := #[]

    -- there seems to be extra 14 bytes at the begginning
    -- there are four uint64, magic number, number of images, x dimension, y dimension
    let _header ← m.read 16 

    for _ in [0:1000000] do
      let n : Nat := 28
      let nums ← m.read (n*n).toUSize
      if nums.size = 0 then
        break
        
      -- byte data to floats 
      -- let mut d : Float^[28,28] := 0
      -- for i in fullRange (Idx 28 × Idx 28) do
      --   let li := (toIdx i).1
      --   d[i] := nums[li]!.toNat.toFloat / 256.0

      data := data.push nums

    return data



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

def printDigit' (digit : ByteArray) : IO Unit := do
  let mut idx := 0
  for i in fullRange (Idx 28) do
    IO.print "|"
    for j in fullRange (Idx 28) do
      let val := digit[idx]!
      if (val > 200) then
        IO.print "#"
      else if (val > 150) then
        IO.print "$"
      else if (val > 50) then
        IO.print "o"
      else if (val > 1) then
        IO.print "."
      else
        IO.print " "
      
      idx := idx + 1

    IO.println "|"



def main : IO Unit := do

  IO.print "loading data ... "
  let data ← loadData
  IO.println "data loaded"

  IO.println "" 
  IO.println s!"number of images: {data.size}" 

  IO.println "+----------------------------+"
  printDigit' data[400]!
  IO.println "+----------------------------+"
  printDigit' data[600]!
  IO.println "+----------------------------+"

