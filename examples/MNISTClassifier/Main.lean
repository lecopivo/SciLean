import examples.MNISTClassifier.DataUtil
import examples.MNISTClassifier.Model

open SciLean


def main : IO Unit := do

  let trainNum := 1000
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

