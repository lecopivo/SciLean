import SciLean.Data.DataArray
import SciLean.Analysis.Calculus.RevFDeriv

namespace SciLean.ML

/--
  Basic machine learning functionality for SciLean.
  
  This implementation focuses on:
  - Table interface for data
  - Back propagation
  - Simple fully connected network
-/

variable {K : Type} [RealScalar K] [PlainDataType K]
variable {n m : Nat}

/-- A table of data with rows and columns -/
structure Table (rowType colType : Type) [IndexType rowType] [IndexType colType] (elemType : Type) where
  data : DataArrayN (DataArrayN elemType colType) rowType
  deriving Inhabited

/-- Get a row from a table -/
def Table.getRow {rowType colType : Type} [IndexType rowType] [IndexType colType] {elemType : Type}
    (table : Table rowType colType elemType) (row : rowType) : DataArrayN elemType colType :=
  table.data[row]

/-- Get a column from a table -/
def Table.getCol {rowType colType : Type} [IndexType rowType] [IndexType colType] {elemType : Type}
    (table : Table rowType colType elemType) (col : colType) : DataArrayN elemType rowType :=
  ⊞ row => table.data[row][col]

/-- A simple fully connected neural network layer -/
structure FCLayer (inputDim outputDim : Nat) where
  weights : K^[outputDim, inputDim]
  biases : K^[outputDim]
  deriving Inhabited

/-- Forward pass through a fully connected layer -/
def FCLayer.forward {inputDim outputDim : Nat} (layer : FCLayer inputDim outputDim) (input : K^[inputDim]) : K^[outputDim] :=
  layer.weights * input + layer.biases

/-- Activation function interface -/
class Activation where
  apply : K → K
  derivative : K → K

/-- ReLU activation function -/
instance : Activation where
  apply x := max x 0
  derivative x := if x > 0 then 1 else 0

/-- Sigmoid activation function -/
def sigmoid : Activation where
  apply x := 1 / (1 + exp (-x))
  derivative x := 
    let s := 1 / (1 + exp (-x))
    s * (1 - s)

/-- A simple neural network with one hidden layer -/
structure SimpleNN (inputDim hiddenDim outputDim : Nat) where
  layer1 : FCLayer inputDim hiddenDim
  layer2 : FCLayer hiddenDim outputDim
  deriving Inhabited

/-- Forward pass through a simple neural network -/
def SimpleNN.forward {inputDim hiddenDim outputDim : Nat} 
    (nn : SimpleNN inputDim hiddenDim outputDim) (input : K^[inputDim]) : K^[outputDim] :=
  let hidden := nn.layer1.forward input
  let activated := ⊞ i => Activation.apply hidden[i]
  nn.layer2.forward activated

/-- Mean squared error loss function -/
def mseLoss {outputDim : Nat} (prediction : K^[outputDim]) (target : K^[outputDim]) : K :=
  let diff := prediction - target
  (diff.dot diff) / outputDim

/-- Backpropagation for a simple neural network -/
def SimpleNN.backprop {inputDim hiddenDim outputDim : Nat} 
    (nn : SimpleNN inputDim hiddenDim outputDim) 
    (input : K^[inputDim]) (target : K^[outputDim]) 
    (learningRate : K) : SimpleNN inputDim hiddenDim outputDim :=
  let forward := fun (nn : SimpleNN inputDim hiddenDim outputDim) => 
    mseLoss (nn.forward input) target
  
  let (_, gradient) := revFDeriv K forward nn
  
  -- Update weights and biases using gradient descent
  { layer1 := {
      weights := nn.layer1.weights - learningRate • gradient.layer1.weights,
      biases := nn.layer1.biases - learningRate • gradient.layer1.biases
    },
    layer2 := {
      weights := nn.layer2.weights - learningRate • gradient.layer2.weights,
      biases := nn.layer2.biases - learningRate • gradient.layer2.biases
    }
  }

end SciLean.ML
