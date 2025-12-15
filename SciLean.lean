import SciLean.AD.FDeriv
import SciLean.AD.FwdFDeriv
import SciLean.AD.HasFDeriv
import SciLean.AD.HasFwdFDeriv
import SciLean.AD.HasRevFDeriv
import SciLean.AD.HasVecFwdFDeriv
import SciLean.AD.HasVecRevFDeriv
import SciLean.AD.RevFDeriv
import SciLean.AD.Rules.Common
import SciLean.AD.Rules.DataArrayN.Det
import SciLean.AD.Rules.DataArrayN.FromRn
import SciLean.AD.Rules.DataArrayN.Logsumexp
import SciLean.AD.Rules.DataArrayN.Minor
import SciLean.AD.Rules.DataArrayN.RSum
import SciLean.AD.Rules.DataArrayN.Reshape
import SciLean.AD.Rules.DataArrayN.ScalAdd
import SciLean.AD.Rules.DataArrayN.Softmax
import SciLean.AD.Rules.DataArrayN.Sum
import SciLean.AD.Rules.DataArrayN.SumMiddleR
import SciLean.AD.Rules.DataArrayN.SumRows
import SciLean.AD.Rules.DataArrayN.ToRn
import SciLean.AD.Rules.Exp
import SciLean.AD.Rules.IndexType.Fold
import SciLean.AD.Rules.IndexType.Max
import SciLean.AD.Rules.IndexType.Min
import SciLean.AD.Rules.IndexType.Sum
import SciLean.AD.Rules.Log
import SciLean.AD.Rules.MatVecMul
import SciLean.AD.Rules.VecMatMul
import SciLean.Algebra.CanonicalBasis
import SciLean.Algebra.Determinant
import SciLean.Algebra.Dimension
import SciLean.Algebra.IsAddGroupHom
import SciLean.Algebra.IsAffineMap
import SciLean.Algebra.IsLinearMap
import SciLean.Algebra.MatrixType.Basic
import SciLean.Algebra.TensorProduct.Assoc
import SciLean.Algebra.TensorProduct.Basic
import SciLean.Algebra.TensorProduct.Curry
import SciLean.Algebra.TensorProduct.MatMul
import SciLean.Algebra.TensorProduct.Pi
import SciLean.Algebra.TensorProduct.Prod
import SciLean.Algebra.TensorProduct.ProdMatrix
import SciLean.Algebra.TensorProduct.ProdMatrixCol
import SciLean.Algebra.TensorProduct.ProdMatrixRow
import SciLean.Algebra.TensorProduct.Self
import SciLean.Algebra.TensorProduct.Swap
import SciLean.Algebra.TensorProduct.Transpose
import SciLean.Algebra.TensorProduct.Util
import SciLean.Algebra.VectorOptimize.Basic
import SciLean.Algebra.VectorOptimize.Init
import SciLean.Analysis.AdjointSpace.Adjoint
import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.AdjointSpace.CanonicalBasis
import SciLean.Analysis.AdjointSpace.Geometry
import SciLean.Analysis.AdjointSpace.HasAdjoint
import SciLean.Analysis.Calculus.ContDiff
import SciLean.Analysis.Calculus.FDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.HasFDeriv
import SciLean.Analysis.Calculus.HasFwdFDeriv
-- import SciLean.Analysis.Calculus.HasParamDerivWithDisc.Common
-- import SciLean.Analysis.Calculus.HasParamDerivWithDisc.Functions
-- import SciLean.Analysis.Calculus.HasParamDerivWithDisc.HasParamFDerivWithDisc
-- import SciLean.Analysis.Calculus.HasParamDerivWithDisc.HasParamFwdFDerivWithDisc
-- import SciLean.Analysis.Calculus.HasParamDerivWithDisc.HasParamRevFDerivWithDisc
import SciLean.Analysis.Calculus.HasRevFDeriv
import SciLean.Analysis.Calculus.HasVecFwdFDeriv
import SciLean.Analysis.Calculus.HasVecRevFDeriv
import SciLean.Analysis.Calculus.Jacobian
import SciLean.Analysis.Calculus.Monad.DifferentiableMonad
import SciLean.Analysis.Calculus.Monad.FwdFDerivMonad
import SciLean.Analysis.Calculus.Monad.HasRevFDerivMonad
import SciLean.Analysis.Calculus.Monad.Id
import SciLean.Analysis.Calculus.Monad.RevFDerivMonad
import SciLean.Analysis.Calculus.Monad.StateT
import SciLean.Analysis.Calculus.Notation.Deriv
import SciLean.Analysis.Calculus.Notation.FwdDeriv
import SciLean.Analysis.Calculus.Notation.Gradient
import SciLean.Analysis.Calculus.Notation.RevDeriv
import SciLean.Analysis.Calculus.Notation.Test
import SciLean.Analysis.Calculus.RevCDeriv
import SciLean.Analysis.Calculus.RevFDeriv
-- import SciLean.Analysis.Diffeology.Array
-- import SciLean.Analysis.Diffeology.ArrayTangentSpace
-- import SciLean.Analysis.Diffeology.Basic
-- import SciLean.Analysis.Diffeology.Connection
-- import SciLean.Analysis.Diffeology.DiffeologyMap
-- import SciLean.Analysis.Diffeology.IsConstantOnPlots
-- import SciLean.Analysis.Diffeology.Option
-- import SciLean.Analysis.Diffeology.OptionInstances
-- import SciLean.Analysis.Diffeology.Pi
-- import SciLean.Analysis.Diffeology.PlotConstant
-- import SciLean.Analysis.Diffeology.PlotHomotopy
-- import SciLean.Analysis.Diffeology.Prod
-- import SciLean.Analysis.Diffeology.Sum
-- import SciLean.Analysis.Diffeology.TangentBundle
-- import SciLean.Analysis.Diffeology.TangentSpace
-- import SciLean.Analysis.Diffeology.Util
-- import SciLean.Analysis.Diffeology.VecDiffeology
import SciLean.Analysis.Matrix
import SciLean.Analysis.MetricSpace
import SciLean.Analysis.Normed.Diffeomorphism
import SciLean.Analysis.Normed.IsContinuousLinearMap
import SciLean.Analysis.Normed.Norm2
import SciLean.Analysis.ODE.OdeSolve
import SciLean.Analysis.Scalar
import SciLean.Analysis.Scalar.Basic
import SciLean.Analysis.Scalar.FloatAsReal
import SciLean.Analysis.Scalar.FloatRealEquiv
import SciLean.Analysis.Scalar.Notation
-- import SciLean.Analysis.Sorry  -- disabled: needs mathlib API update for MulAction
import SciLean.Analysis.SpecialFunctions.GaborWavelet
import SciLean.Analysis.SpecialFunctions.Gaussian
import SciLean.Analysis.SpecialFunctions.Inner
import SciLean.Analysis.SpecialFunctions.MultiGamma
import SciLean.Analysis.SpecialFunctions.Norm2
import SciLean.Analysis.SpecialFunctions.Pow
import SciLean.Analysis.SpecialFunctions.StarRingEnd
import SciLean.Analysis.SpecialFunctions.Trigonometric
-- import SciLean.Core_old.Approx.ApproxLimit
-- import SciLean.Core_old.Approx.ApproxSolution
-- import SciLean.Core_old.Approx.Basic
-- import SciLean.Core_old.Approx.Test
-- import SciLean.Core_old.Distribution
-- import SciLean.Core_old.Distribution.Basic
-- import SciLean.Core_old.Distribution.BungeeTest
-- import SciLean.Core_old.Distribution.Doodle
-- import SciLean.Core_old.Distribution.Doodle2
-- import SciLean.Core_old.Distribution.Eval
-- import SciLean.Core_old.Distribution.HadDerivUnderBind
-- import SciLean.Core_old.Distribution.ParametricDistribDeriv
-- import SciLean.Core_old.Distribution.ParametricDistribFwdDeriv
-- import SciLean.Core_old.Distribution.ParametricDistribRevDeriv
-- import SciLean.Core_old.Distribution.RestrictToLevelSet
-- import SciLean.Core_old.Distribution.SimpAttr
-- import SciLean.Core_old.Distribution.SimpleExamples
-- import SciLean.Core_old.Distribution.SimpleExamples2D
-- import SciLean.Core_old.Distribution.SurfaceDirac
-- import SciLean.Core_old.Distribution.TestFunction
-- import SciLean.Core_old.Distribution.VarInference
-- import SciLean.Core_old.FloatAsReal
-- import SciLean.Core_old.Function
-- import SciLean.Core_old.FunctionPropositions
-- import SciLean.Core_old.FunctionPropositions.Bijective
-- import SciLean.Core_old.FunctionPropositions.CDifferentiable
-- import SciLean.Core_old.FunctionPropositions.ContCDiff
-- import SciLean.Core_old.FunctionPropositions.Diffeomorphism
-- import SciLean.Core_old.FunctionPropositions.Differentiable
-- import SciLean.Core_old.FunctionPropositions.HasAdjDiff
-- import SciLean.Core_old.FunctionPropositions.HasInvDiff
-- import SciLean.Core_old.FunctionPropositions.HasSemiAdjoint
-- import SciLean.Core_old.FunctionPropositions.IsAffineMap
-- import SciLean.Core_old.FunctionPropositions.IsContinuousLinearMap
-- import SciLean.Core_old.FunctionPropositions.IsLinearMap
-- import SciLean.Core_old.FunctionPropositions.IsSmoothLinearMap
-- import SciLean.Core_old.FunctionSpaces
-- import SciLean.Core_old.FunctionSpaces.ContCDiffMap
-- import SciLean.Core_old.FunctionSpaces.ContCDiffMapFD
-- import SciLean.Core_old.FunctionSpaces.SmoothLinearMap
-- import SciLean.Core_old.FunctionTransformations
-- import SciLean.Core_old.FunctionTransformations.Broadcast
-- import SciLean.Core_old.FunctionTransformations.CDeriv
-- import SciLean.Core_old.FunctionTransformations.Complexify
-- import SciLean.Core_old.FunctionTransformations.Determinant
-- import SciLean.Core_old.FunctionTransformations.FDeriv
-- import SciLean.Core_old.FunctionTransformations.FwdDeriv
-- import SciLean.Core_old.FunctionTransformations.FwdFDeriv
-- import SciLean.Core_old.FunctionTransformations.InvFun
-- import SciLean.Core_old.FunctionTransformations.Isomorph
-- import SciLean.Core_old.FunctionTransformations.Isomorph.RealToFloat
-- import SciLean.Core_old.FunctionTransformations.Jacobian
-- import SciLean.Core_old.FunctionTransformations.Preimage
-- import SciLean.Core_old.FunctionTransformations.RevDeriv
-- import SciLean.Core_old.FunctionTransformations.RevDeriv2
-- import SciLean.Core_old.FunctionTransformations.RevFDeriv
-- import SciLean.Core_old.FunctionTransformations.SemiAdjoint
-- import SciLean.Core_old.FunctionTransformations.ToMatrix
-- import SciLean.Core_old.Functions.ArgMinMax
-- import SciLean.Core_old.Functions.Exp
-- import SciLean.Core_old.Functions.Gaussian
-- import SciLean.Core_old.Functions.Inner
-- import SciLean.Core_old.Functions.Norm2
-- import SciLean.Core_old.Functions.Pow
-- import SciLean.Core_old.Functions.Trigonometric
-- import SciLean.Core_old.Integral.CIntegral
-- import SciLean.Core_old.Integral.HasDerivUnderIntegral
-- import SciLean.Core_old.Integral.MovingDomain
-- import SciLean.Core_old.Integral.RestrictToLevelSet
-- import SciLean.Core_old.Integral.TestBungee
-- import SciLean.Core_old.Integral.VectorIntegral
-- import SciLean.Core_old.LinearAlgebra.GramSchmidt
-- import SciLean.Core_old.LinearAlgebra.GramSchmidt.Basic
-- import SciLean.Core_old.LinearAlgebra.GramSchmidt.Properties
-- import SciLean.Core_old.Meta.ExtendContext
-- import SciLean.Core_old.Meta.GenerateBasic
-- import SciLean.Core_old.Meta.GenerateFunProp
-- import SciLean.Core_old.Meta.GenerateFunTrans
-- import SciLean.Core_old.Meta.GenerateFunTransTest
-- import SciLean.Core_old.Meta.GenerateFwdCDeriv
-- import SciLean.Core_old.Meta.GenerateInit
-- import SciLean.Core_old.Meta.GenerateLinearMapSimp
-- import SciLean.Core_old.Meta.GenerateRevCDeriv'
-- import SciLean.Core_old.Meta.GenerateRevCDeriv
-- import SciLean.Core_old.Meta.GenerateRevDeriv
-- import SciLean.Core_old.Meta.ParametrizeFVars
-- import SciLean.Core_old.Meta.ToAnyPoint
-- import SciLean.Core_old.Monads
-- import SciLean.Core_old.Monads.ForIn
-- import SciLean.Core_old.Monads.ForInStep
-- import SciLean.Core_old.Monads.ForInTests
-- import SciLean.Core_old.Monads.FwdDerivMonad
-- import SciLean.Core_old.Monads.IO
-- import SciLean.Core_old.Monads.Id
-- import SciLean.Core_old.Monads.MProd
-- import SciLean.Core_old.Monads.RevDerivMonad
-- import SciLean.Core_old.Monads.StateT
-- import SciLean.Core_old.Notation
-- import SciLean.Core_old.Notation.CDeriv
-- import SciLean.Core_old.Notation.Do
-- import SciLean.Core_old.Notation.FwdDeriv
-- import SciLean.Core_old.Notation.Gradient
-- import SciLean.Core_old.Notation.RevCDeriv
-- import SciLean.Core_old.Notation.Symdiff
-- import SciLean.Core_old.Notation.Test
-- import SciLean.Core_old.NotationOverField
-- import SciLean.Core_old.Objects.BroadcastType
-- import SciLean.Core_old.Objects.FinVec
-- import SciLean.Core_old.Objects.IsReal
-- import SciLean.Core_old.Objects.IsomorphicType
-- import SciLean.Core_old.Objects.IsomorphicType.RealToFloat
-- import SciLean.Core_old.Objects.Scalar
-- import SciLean.Core_old.Objects.SemiInnerProductSpace
-- import SciLean.Core_old.Objects.Vec
-- import SciLean.Core_old.Rand
-- import SciLean.Core_old.Rand.Condition
-- import SciLean.Core_old.Rand.Distributions.Flip
-- import SciLean.Core_old.Rand.Distributions.FlipTest
-- import SciLean.Core_old.Rand.Distributions.ListSumTest
-- import SciLean.Core_old.Rand.Distributions.Normal
-- import SciLean.Core_old.Rand.Distributions.Sphere
-- import SciLean.Core_old.Rand.Distributions.Uniform
-- import SciLean.Core_old.Rand.Distributions.WalkOnSpheres
-- import SciLean.Core_old.Rand.Doodle
-- import SciLean.Core_old.Rand.ExpectedValue
-- import SciLean.Core_old.Rand.IsAffineRandMap
-- import SciLean.Core_old.Rand.Model
-- import SciLean.Core_old.Rand.PullMean
-- import SciLean.Core_old.Rand.PushPullExpectation
-- import SciLean.Core_old.Rand.Rand
-- import SciLean.Core_old.Rand.RandWithTrace
-- import SciLean.Core_old.Rand.SimpAttr
-- import SciLean.Core_old.Rand.Tactic
-- import SciLean.Core_old.Rand.VariationalInference
-- import SciLean.Core_old.Simp
-- import SciLean.Core_old.Transformations.BoundingBall
-- import SciLean.Core_old.Transformations.HasParamDerivWithJumps.Common
-- import SciLean.Core_old.Transformations.HasParamDerivWithJumps.Functions
-- import SciLean.Core_old.Transformations.HasParamDerivWithJumps.HasParamFDerivWithJumps
-- import SciLean.Core_old.Transformations.HasParamDerivWithJumps.HasParamFwdFDerivWithJumps
-- import SciLean.Core_old.Transformations.HasParamDerivWithJumps.HasParamRevFDerivWithJumps
-- import SciLean.Core_old.Transformations.RnDeriv
-- import SciLean.Core_old.Transformations.SurfaceParametrization
-- import SciLean.Core_old.old.AdjDiff
-- import SciLean.Core_old.old.AdjDiffDep
-- import SciLean.Core_old.old.Adjoint
-- import SciLean.Core_old.old.AdjointHardCases
-- import SciLean.Core_old.old.Attributes
-- import SciLean.Core_old.old.AutoDiffSimps
-- import SciLean.Core_old.old.Connection.Basic
-- import SciLean.Core_old.old.CoreFunctions
-- import SciLean.Core_old.old.Defs
-- import SciLean.Core_old.old.Diff
-- import SciLean.Core_old.old.DiffeologicalSpaces.Diff
-- import SciLean.Core_old.old.DiffeologicalSpaces.IsSmoothDep
-- import SciLean.Core_old.old.Differential
-- import SciLean.Core_old.old.DifferentialDep
-- import SciLean.Core_old.old.DifferentialSmooth
-- import SciLean.Core_old.old.Extra
-- import SciLean.Core_old.old.FinVec
-- import SciLean.Core_old.old.FunPropCore
-- import SciLean.Core_old.old.HasAdjDiff
-- import SciLean.Core_old.old.HasAdjDiffDep
-- import SciLean.Core_old.old.HasAdjoint
-- import SciLean.Core_old.old.Hilbert
-- import SciLean.Core_old.old.HilbertDiff
-- import SciLean.Core_old.old.Integral
-- import SciLean.Core_old.old.IntegralDoodle
-- import SciLean.Core_old.old.IntegralProperties
-- import SciLean.Core_old.old.InvFun
-- import SciLean.Core_old.old.InvMap
-- import SciLean.Core_old.old.IsInv
-- import SciLean.Core_old.old.IsLin
-- import SciLean.Core_old.old.IsSmooth
-- import SciLean.Core_old.old.IsSmoothDep
-- import SciLean.Core_old.old.LinMap
-- import SciLean.Core_old.old.Meta.BracketedBinder
-- import SciLean.Core_old.old.Meta.FunctionProperty.Apply
-- import SciLean.Core_old.old.Meta.FunctionProperty.CompTheorem
-- import SciLean.Core_old.old.Meta.FunctionProperty.Decl
-- import SciLean.Core_old.old.Meta.FunctionProperty.EnvExtension
-- import SciLean.Core_old.old.Meta.FunctionProperty.LocalContext
-- import SciLean.Core_old.old.Meta.FunctionProperty.NormalTheorem
-- import SciLean.Core_old.old.Meta.FunctionProperty.PropertyMap
-- import SciLean.Core_old.old.Meta.FunctionProperty.Syntax
-- import SciLean.Core_old.old.Meta.FunctionProperty.Test
-- import SciLean.Core_old.old.Real
-- import SciLean.Core_old.old.RealFunctions
-- import SciLean.Core_old.old.SemiInnerProductSpace
-- import SciLean.Core_old.old.SmoothMap
-- import SciLean.Core_old.old.Tactic.FunctionTransformation
-- import SciLean.Core_old.old.Tactic.FunctionTransformation.Autodiff
-- import SciLean.Core_old.old.Tactic.FunctionTransformation.Core
-- import SciLean.Core_old.old.Tactic.FunctionTransformation.FunTelescope
-- import SciLean.Core_old.old.Tactic.FunctionTransformation.Init
-- import SciLean.Core_old.old.Tactic.FunctionTransformation.PropertyAutoImpl
-- import SciLean.Core_old.old.Tactic.FunctionTransformation.Test
-- import SciLean.Core_old.old.TensorProduct
-- import SciLean.Core_old.old.UnsafeAD
-- import SciLean.Core_old.old.VariationalCalculus
-- import SciLean.Core_old.old.VariationalCalculus.Examples
-- import SciLean.Core_old.old.Vec
import SciLean.Compiler.LazyTensor
import SciLean.Data.ArrayLike
import SciLean.Data.ArrayOperations.Algebra
import SciLean.Data.ArrayOperations.Basic
import SciLean.Data.ArrayOperations.Operations
import SciLean.Data.ArrayOperations.Operations.GetElem
import SciLean.Data.ArrayOperations.Operations.MapIdxMonoAcc
import SciLean.Data.ArrayOperations.Operations.OfFn
import SciLean.Data.ArrayOperations.Operations.SetElem
import SciLean.Data.ArraySet
import SciLean.Data.ArrayType
-- import SciLean.Data.ArrayType.Algebra_old
import SciLean.Data.ArrayType.Basic
import SciLean.Data.ArrayType.Notation
-- import SciLean.Data.ArrayType.Properties_old
import SciLean.Data.ByteArray
import SciLean.Data.ColProd
import SciLean.Data.Curry
import SciLean.Data.DataArray
import SciLean.Data.DataArray.Algebra
import SciLean.Data.DataArray.Basis
import SciLean.Data.DataArray.DataArray
import SciLean.Data.DataArray.DataArrayEquiv
import SciLean.Data.DataArray.Float
import SciLean.Data.DataArray.FloatN
import SciLean.Data.DataArray.FloatNN
import SciLean.Data.DataArray.MatrixType
import SciLean.Data.DataArray.Operations
import SciLean.Data.DataArray.Operations.Col
import SciLean.Data.DataArray.Operations.Curry
import SciLean.Data.DataArray.Operations.Row
import SciLean.Data.DataArray.Operations.Uncurry
import SciLean.Data.DataArray.Random
-- import SciLean.Data.DataArray.Operations_old
-- import SciLean.Data.DataArray.Operations_old.AntiSymmPart
-- import SciLean.Data.DataArray.Operations_old.Cross
-- import SciLean.Data.DataArray.Operations_old.CrossMatrix
-- import SciLean.Data.DataArray.Operations_old.Curry
-- import SciLean.Data.DataArray.Operations_old.Det
-- import SciLean.Data.DataArray.Operations_old.Diag
-- import SciLean.Data.DataArray.Operations_old.Diagonal
-- import SciLean.Data.DataArray.Operations_old.Dot
-- import SciLean.Data.DataArray.Operations_old.Exp
-- import SciLean.Data.DataArray.Operations_old.GaussianS
-- import SciLean.Data.DataArray.Operations_old.Inv
-- import SciLean.Data.DataArray.Operations_old.Log
-- import SciLean.Data.DataArray.Operations_old.Logsumexp
-- import SciLean.Data.DataArray.Operations_old.LowerTriangular
-- import SciLean.Data.DataArray.Operations_old.LowerTriangularPart
-- import SciLean.Data.DataArray.Operations_old.Matmul
-- import SciLean.Data.DataArray.Operations_old.Multiply
-- import SciLean.Data.DataArray.Operations_old.NPow
-- import SciLean.Data.DataArray.Operations_old.Outerprod
-- import SciLean.Data.DataArray.Operations_old.Simps
-- import SciLean.Data.DataArray.Operations_old.Softmax
-- import SciLean.Data.DataArray.Operations_old.Solve
-- import SciLean.Data.DataArray.Operations_old.Sum
-- import SciLean.Data.DataArray.Operations_old.Trace
-- import SciLean.Data.DataArray.Operations_old.Transpose
-- import SciLean.Data.DataArray.Operations_old.Uncurry
-- import SciLean.Data.DataArray.Operations_old.Vecmul
import SciLean.Data.DataArray.PlainDataType
import SciLean.Data.DataArray.RnEquiv
import SciLean.Data.DataArray.TensorOperations
import SciLean.Data.DataArray.TensorProduct
import SciLean.Data.TensorBackend
-- import SciLean.Data.TensorBackendMetal  -- Metal backend (requires Metal.lean FFI)
import SciLean.Data.FinProd
import SciLean.Data.Float
import SciLean.Data.FloatArray
import SciLean.Data.Function
import SciLean.Data.Idx
import SciLean.Data.Idx.Basic
import SciLean.Data.Idx.GetElemIdx
import SciLean.Data.IndexType
import SciLean.Data.Instances.Sigma
import SciLean.Data.Int64
import SciLean.Data.ListN
import SciLean.Data.Nat
import SciLean.Data.Prod
import SciLean.Data.Random
-- import SciLean.Data.SparseMatrix.Basic  -- disabled: needs mathlib API update for List.Sorted
import SciLean.Data.StructType
-- import SciLean.Data.StructType.Algebra  -- disabled: file moved to Algebra.lean.disabled
import SciLean.Data.StructType.Basic
import SciLean.Data.Vector
import SciLean.Data.VectorType.Base
-- import SciLean.Data.VectorType.VectorType_old.BaseSimps
-- import SciLean.Data.VectorType.VectorType_old.Basic
-- import SciLean.Data.VectorType.VectorType_old.BinOps
-- import SciLean.Data.VectorType.VectorType_old.Init
-- import SciLean.Data.VectorType.VectorType_old.Operations.Axpby
-- import SciLean.Data.VectorType.VectorType_old.Operations.Axpy
-- import SciLean.Data.VectorType.VectorType_old.Operations.Dot
-- import SciLean.Data.VectorType.VectorType_old.Operations.Exp
-- import SciLean.Data.VectorType.VectorType_old.Operations.FromVec
-- import SciLean.Data.VectorType.VectorType_old.Operations.Logsumexp
-- import SciLean.Data.VectorType.VectorType_old.Operations.MapIdx
-- import SciLean.Data.VectorType.VectorType_old.Operations.Max
-- import SciLean.Data.VectorType.VectorType_old.Operations.Mul
-- import SciLean.Data.VectorType.VectorType_old.Operations.Scal
-- import SciLean.Data.VectorType.VectorType_old.Operations.ScalAdd
-- import SciLean.Data.VectorType.VectorType_old.Operations.Set
-- import SciLean.Data.VectorType.VectorType_old.Operations.Softmax
-- import SciLean.Data.VectorType.VectorType_old.Operations.Sum
-- import SciLean.Data.VectorType.VectorType_old.Operations.ToVec
-- import SciLean.Data.VectorType.VectorType_old.Optimize
-- import SciLean.Data.VectorType.VectorType_old.Prod
-- import SciLean.Data.VectorType.VectorType_old.Scalar
-- import SciLean.Data.VectorType.VectorType_old.Subvector
-- import SciLean.Doodle
-- import SciLean.Doodle14
-- import SciLean.Examples.GMM.Main
-- import SciLean.Examples.GMM.Objective
-- import SciLean.Examples.GMM.ObjectiveDirect
-- import SciLean.Examples.GMM.Simps
-- import SciLean.Examples.GMM.SumSimproc
-- import SciLean.Examples.GMM.Util
import SciLean.FFI
import SciLean.FFI.ByteArray
import SciLean.FFI.Float
import SciLean.FFI.FloatArray
-- import SciLean.Geometry.Bezier
import SciLean.Geometry.BoundingBall
import SciLean.Geometry.FrontierSpeed
-- import SciLean.Geometry.Shape.AxisAlignedBox
-- import SciLean.Geometry.Shape.Basic
-- import SciLean.Geometry.Shape.BasicShapes
-- import SciLean.Geometry.Shape.Rotation
-- import SciLean.Geometry.Shape.Segment
-- import SciLean.Geometry.Shape.Shape
-- import SciLean.Geometry.Shape.Simplex
-- import SciLean.Geometry.Shape.Sphere
-- import SciLean.Geometry.Shape.TransformedShape
-- import SciLean.Geometry.Shape.Triangle
import SciLean.Geometry.SurfaceParametrization
import SciLean.Lean.Array
import SciLean.Lean.Expr
import SciLean.Lean.HashMap
import SciLean.Lean.MergeMapDeclarationExtension
import SciLean.Lean.Meta.Basic
import SciLean.Lean.Meta.Replace
import SciLean.Lean.Meta.Structure
import SciLean.Lean.Meta.Uncurry
import SciLean.Lean.Name
import SciLean.Lean.String
import SciLean.Lean.ToSSA
import SciLean.Logic.Function.Basic
import SciLean.Logic.Function.Bijective
import SciLean.Logic.Function.Constant
import SciLean.Logic.Function.InvFun
import SciLean.Logic.Function.Preimage
import SciLean.Logic.Function.Sort
import SciLean.Logic.If
import SciLean.Logic.Isomorph.Isomorph
import SciLean.Logic.Isomorph.IsomorphicType
import SciLean.Logic.Isomorph.RealToFloat.Basic
import SciLean.Logic.Isomorph.RealToFloat.Type
-- import SciLean.Mathlib_old.Analysis.AdjointSpace.Adjoint
-- import SciLean.Mathlib_old.Analysis.AdjointSpace.Basic
-- import SciLean.Mathlib_old.Analysis.AdjointSpace.Dual
-- import SciLean.Mathlib_old.Analysis.AdjointSpace.Geometry
-- import SciLean.Mathlib_old.Analysis.ConvenientSpace.Basic
-- import SciLean.Mathlib_old.Analysis.InnerProductSpace.Prod
-- import SciLean.Mathlib_old.Analysis.MetricSpace
-- import SciLean.Mathlib_old.LinearAlgebra.Basis
-- import SciLean.Mathlib_old.MeasureTheory.Unit
-- import SciLean.Mathlib_old.MeasureTheory.WeakIntegral
-- import SciLean.Mathlib_old.Set
import SciLean.MeasureTheory.RnDeriv
import SciLean.MeasureTheory.WeakIntegral
-- import SciLean.Meta.DerivingAlgebra
-- import SciLean.Meta.DerivingOp
import SciLean.Meta.GenerateAddGroupHomSimp
import SciLean.Meta.GenerateFunProp
import SciLean.Meta.GenerateFunTrans
import SciLean.Meta.GenerateLinearMapSimp
import SciLean.Meta.Notation.Do
import SciLean.Meta.Notation.Einsum
import SciLean.Meta.Notation.Let'
import SciLean.Meta.SetSynthOrder
import SciLean.Meta.SimpAttr
import SciLean.Meta.SimpCore
import SciLean.Modules.DDG.SurfaceMesh
import SciLean.Modules.DDG.Trace
-- import SciLean.Modules.FiniteElement.Mesh.Circle
-- import SciLean.Modules.FiniteElement.Mesh.Line
-- import SciLean.Modules.FiniteElement.Mesh.Prism
-- import SciLean.Modules.FiniteElement.Mesh.PrismClosestPoint
-- import SciLean.Modules.FiniteElement.Mesh.PrismFiniteElement
-- import SciLean.Modules.FiniteElement.Mesh.PrismRepr
-- import SciLean.Modules.FiniteElement.Mesh.PrismTest
-- import SciLean.Modules.FiniteElement.Mesh.PrismaticMesh
-- import SciLean.Modules.FiniteElement.Mesh.PrismaticSet
-- import SciLean.Modules.FiniteElement.Mesh.Segment
-- import SciLean.Modules.FiniteElement.Mesh.TriangularMesh
-- import SciLean.Modules.Geometry.Bezier
-- import SciLean.Modules.Geometry.Shape
-- import SciLean.Modules.Geometry.Shape.AxisAlignedBox
-- import SciLean.Modules.Geometry.Shape.BasicShapes
-- import SciLean.Modules.Geometry.Shape.Rotation
-- import SciLean.Modules.Geometry.Shape.Shape
-- import SciLean.Modules.Geometry.Shape.Simplex
-- import SciLean.Modules.Geometry.Shape.Sphere
-- import SciLean.Modules.Geometry.Shape.TransformedShape
-- import SciLean.Modules.Geometry.Shape.Triangle
-- import SciLean.Modules.Interpolation.Interpolate
-- import SciLean.Modules.ML
-- import SciLean.Modules.ML.Activation
-- import SciLean.Modules.ML.Convolution
-- import SciLean.Modules.ML.Dense
-- import SciLean.Modules.ML.Doodle
-- import SciLean.Modules.ML.Loss
-- import SciLean.Modules.ML.MNIST
-- import SciLean.Modules.ML.Pool
-- import SciLean.Modules.ML.SoftMax
-- import SciLean.Modules.ML.XLA.Concatenate
-- import SciLean.Modules.ML.XLA.ConvWithBatchFeature
-- import SciLean.Modules.ML.XLA.ConvWithPadding
-- import SciLean.Modules.ML.XLA.ConvWithPaddingStride
-- import SciLean.Modules.ML.XLA.Convolution
-- import SciLean.Modules.ML.XLA.DotGeneral
-- import SciLean.Modules.ML.XLA.Pad
-- import SciLean.Modules.ML.XLA.Slice
-- import SciLean.Modules.ML.XLA.Split
-- import SciLean.Modules.ML.XLA.TensorIndex
-- import SciLean.Modules.ML.XLA.Transpose
-- import SciLean.Modules.PhysicalUnits.PhysicalUnits
-- import SciLean.Modules.Prob.ADTheorems
-- import SciLean.Modules.Prob.DRand
-- import SciLean.Modules.Prob.DerivUnderIntegralSign
-- import SciLean.Modules.Prob.Dice
-- import SciLean.Modules.Prob.DistribDeriv.DistribDeriv
-- import SciLean.Modules.Prob.DistribDeriv.DistribFwdDeriv
-- import SciLean.Modules.Prob.DistribDeriv.Distribution
-- import SciLean.Modules.Prob.DistribDeriv.Flip
-- import SciLean.Modules.Prob.DistribDeriv.Measure
-- import SciLean.Modules.Prob.DistribDeriv.Normal
-- import SciLean.Modules.Prob.DistribDeriv.Pure
-- import SciLean.Modules.Prob.DistribDeriv.Uniform
-- import SciLean.Modules.Prob.Distributions.Flip
-- import SciLean.Modules.Prob.Distributions.FlipTest
-- import SciLean.Modules.Prob.Distributions.Normal
-- import SciLean.Modules.Prob.Distributions.Test
-- import SciLean.Modules.Prob.Distributions.Uniform
-- import SciLean.Modules.Prob.Distributions.UniformTest
-- import SciLean.Modules.Prob.Doodle
-- import SciLean.Modules.Prob.Erased
-- import SciLean.Modules.Prob.FDRand
-- import SciLean.Modules.Prob.FwdDeriv
-- import SciLean.Modules.Prob.Init
-- import SciLean.Modules.Prob.LiftLets
-- import SciLean.Modules.Prob.NormalTest
-- import SciLean.Modules.Prob.PushPullE
-- import SciLean.Modules.Prob.RDRand
-- import SciLean.Modules.Prob.Rand
-- import SciLean.Modules.Prob.Rand2
-- import SciLean.Modules.Prob.RandDeriv
-- import SciLean.Modules.Prob.RandFwdDeriv
-- import SciLean.Modules.Prob.Simps
-- import SciLean.Modules.Prob.Tactic
-- import SciLean.Modules.Prob.Test
-- import SciLean.Modules.Prob.TestFunctionExtension
-- import SciLean.Modules.Prob.ToMathlib
-- import SciLean.Modules.SolversAndOptimizers.GradientDescent
-- import SciLean.Modules.SolversAndOptimizers.NewtonSolver
-- import SciLean.Modules.SolversAndOptimizers.NewtonSolverTest
-- import SciLean.Modules.Symbolic.Quot.Algebra
-- import SciLean.Modules.Symbolic.Quot.Basic
-- import SciLean.Modules.Symbolic.Quot.FreeMonoid
-- import SciLean.Modules.Symbolic.Quot.Monomial
-- import SciLean.Modules.Symbolic.Quot.QuotQ
-- import SciLean.Modules.Symbolic.Quot.SQuot
-- import SciLean.Modules.Symbolic.Quot.SymMonoid
-- import SciLean.Modules.Symbolic.Quotient
-- import SciLean.Modules.Symbolic.Quotient.GradedQuotient
-- import SciLean.Modules.Symbolic.Quotient.GradedSetoid
-- import SciLean.Modules.Symbolic.Quotient.Lattice
-- import SciLean.Modules.Symbolic.Quotient.Setoid
-- import SciLean.Modules.Symbolic.Symbolic.AltPolynomial
-- import SciLean.Modules.Symbolic.Symbolic.Basic
-- import SciLean.Modules.Symbolic.Symbolic.FreeAlgebra
-- import SciLean.Modules.Symbolic.Symbolic.Monomial
-- import SciLean.Modules.Symbolic.Symbolic.OrthogonalPolynomials
-- import SciLean.Modules.Symbolic.Symbolic.Symbolic
import SciLean.Numerics.ODE.BackwardEuler
import SciLean.Numerics.ODE.Basic
import SciLean.Numerics.ODE.ForwardEuler
import SciLean.Numerics.ODE.Solvers
import SciLean.Numerics.ODE.RungeKutta
import SciLean.Numerics.Optimization.ArgMin
import SciLean.Numerics.Optimization.Optimjl
import SciLean.Numerics.Optimization.Optimjl.LinerSearches.BackTracking
import SciLean.Numerics.Optimization.Optimjl.LinerSearches.Types
import SciLean.Numerics.Optimization.Optimjl.Multivariate.Optimize.Optimize
import SciLean.Numerics.Optimization.Optimjl.Multivariate.Solvers.FirstOrder.BFGS
import SciLean.Numerics.Optimization.Optimjl.Multivariate.Solvers.FirstOrder.LBFGS
import SciLean.Numerics.Optimization.Optimjl.Utilities.Types
import SciLean.Probability.Distributions.Flip
import SciLean.Probability.Distributions.Normal
import SciLean.Probability.Distributions.Uniform
import SciLean.Probability.Distributions.WalkOnSpheres
import SciLean.Probability.IsAffineRandMap
import SciLean.Probability.PullMean
import SciLean.Probability.PushPullExpectation
import SciLean.Probability.Rand
import SciLean.Probability.RandT
import SciLean.Probability.RandWithTrace
import SciLean.Probability.SimpAttr
import SciLean.Probability.Tactic
-- import SciLean.SpecialFunctions.Convolution
-- import SciLean.SpecialFunctions.CrossProduct
-- import SciLean.SpecialFunctions.Divergence
-- import SciLean.SpecialFunctions.EpsLog
-- import SciLean.SpecialFunctions.EpsNorm
-- import SciLean.SpecialFunctions.EpsPow
-- import SciLean.SpecialFunctions.EpsRotate
-- import SciLean.SpecialFunctions.Exp
-- import SciLean.SpecialFunctions.FFT
-- import SciLean.SpecialFunctions.Limit
-- import SciLean.SpecialFunctions.Rotate
-- import SciLean.SpecialFunctions.Trigonometric
import SciLean.Tactic.AnalyzeConstLambda
import SciLean.Tactic.AnalyzeLambda
import SciLean.Tactic.Autodiff
import SciLean.Tactic.Basic
import SciLean.Tactic.CompiledTactics
import SciLean.Tactic.ConvAssign
import SciLean.Tactic.ConvIf
import SciLean.Tactic.ConvInduction
import SciLean.Tactic.DFunLikeCoeZetaDelta
import SciLean.Tactic.DataSynth.Attr
import SciLean.Tactic.DataSynth.Decl
import SciLean.Tactic.DataSynth.DefDataSynth
import SciLean.Tactic.DataSynth.Elab
import SciLean.Tactic.DataSynth.Main
import SciLean.Tactic.DataSynth.Simproc
import SciLean.Tactic.DataSynth.Theorems
import SciLean.Tactic.DataSynth.Types
import SciLean.Tactic.FunTrans.Attr
import SciLean.Tactic.FunTrans.Core
import SciLean.Tactic.FunTrans.Decl
import SciLean.Tactic.FunTrans.Elab
import SciLean.Tactic.FunTrans.Theorems
import SciLean.Tactic.FunTrans.Types
import SciLean.Tactic.GTrans
import SciLean.Tactic.GTrans.Attr
import SciLean.Tactic.GTrans.Core
import SciLean.Tactic.GTrans.Decl
import SciLean.Tactic.GTrans.Elab
import SciLean.Tactic.GTrans.MetaLCtxM
import SciLean.Tactic.GTrans.Theorems
import SciLean.Tactic.IfLetNormalize
import SciLean.Tactic.IfPull
import SciLean.Tactic.InferVar
import SciLean.Tactic.LFunTrans
import SciLean.Tactic.LSimp
import SciLean.Tactic.LSimp.Elab
import SciLean.Tactic.LSimp.Main
import SciLean.Tactic.LSimp.Types
import SciLean.Tactic.LetEnter
import SciLean.Tactic.LetNormalize
import SciLean.Tactic.LetNormalize2
import SciLean.Tactic.LetUtils
import SciLean.Tactic.MetaFunction.Decl
import SciLean.Tactic.MetaFunction.Def
import SciLean.Tactic.MoveTerms
import SciLean.Tactic.OptimizeIndexAccess
import SciLean.Tactic.OptimizeIndexAccessInit
import SciLean.Tactic.PullLimitOut
import SciLean.Tactic.RefinedSimp
import SciLean.Tactic.SimpleProxyType
import SciLean.Tactic.StructuralInverse
import SciLean.Tactic.StructureDecomposition
import SciLean.Tactic.TimeTactic
import SciLean.Tactic.UnsafeAD
import SciLean.Topology.Continuous
import SciLean.Util.Alternatives
import SciLean.Util.Approx.ApproxLimit
import SciLean.Util.Approx.ApproxSolution
import SciLean.Util.Approx.Basic
import SciLean.Util.DefOptimize
import SciLean.Util.HoldLet
import SciLean.Util.HoldLetProperties
import SciLean.Util.Limit
import SciLean.Util.Profile
import SciLean.Util.RecVal
import SciLean.Util.RewriteBy
import SciLean.Util.SolveFun
import SciLean.Util.SorryProof
