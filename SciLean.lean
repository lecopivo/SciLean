import SciLean.Algebra.Determinant
import SciLean.Algebra.IsAddGroupHom
import SciLean.Algebra.IsAffineMap
import SciLean.Algebra.IsLinearMap
import SciLean.Analysis.AdjointSpace.Adjoint
import SciLean.Analysis.AdjointSpace.AdjointProj
import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.AdjointSpace.Geometry
import SciLean.Analysis.Calculus.CDeriv
import SciLean.Analysis.Calculus.FDeriv
import SciLean.Analysis.Calculus.FwdCDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
-- import SciLean.Analysis.Calculus.HasParamDerivWithDisc.Common
-- import SciLean.Analysis.Calculus.HasParamDerivWithDisc.Functions
-- import SciLean.Analysis.Calculus.HasParamDerivWithDisc.HasParamFDerivWithDisc
-- import SciLean.Analysis.Calculus.HasParamDerivWithDisc.HasParamFwdFDerivWithDisc
-- import SciLean.Analysis.Calculus.HasParamDerivWithDisc.HasParamRevFDerivWithDisc
import SciLean.Analysis.Calculus.Jacobian
import SciLean.Analysis.Calculus.Monad.DifferentiableMonad
import SciLean.Analysis.Calculus.Monad.FwdFDerivMonad
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
import SciLean.Analysis.Calculus.RevFDerivProj
import SciLean.Analysis.Convenient.CDifferentiable
import SciLean.Analysis.Convenient.ContCDiff
import SciLean.Analysis.Convenient.Curve
import SciLean.Analysis.Convenient.FinVec
import SciLean.Analysis.Convenient.HasAdjDiff
import SciLean.Analysis.Convenient.HasSemiAdjoint
import SciLean.Analysis.Convenient.IsSmoothLinearMap
import SciLean.Analysis.Convenient.SemiAdjoint
import SciLean.Analysis.Convenient.SemiInnerProductSpace
import SciLean.Analysis.Convenient.Vec
import SciLean.Analysis.FunctionSpaces.ContCDiffMap
import SciLean.Analysis.FunctionSpaces.ContCDiffMapFD
import SciLean.Analysis.FunctionSpaces.SmoothLinearMap
import SciLean.Analysis.MetricSpace
import SciLean.Analysis.Normed.Diffeomorphism
import SciLean.Analysis.Normed.IsContinuousLinearMap
import SciLean.Analysis.ODE.OdeSolve
import SciLean.Analysis.Scalar
import SciLean.Analysis.Scalar.Basic
import SciLean.Analysis.Scalar.FloatAsReal
import SciLean.Analysis.Scalar.Notation
import SciLean.Analysis.SpecialFunctions.Exp
import SciLean.Analysis.SpecialFunctions.Gaussian
import SciLean.Analysis.SpecialFunctions.Inner
import SciLean.Analysis.SpecialFunctions.Log
import SciLean.Analysis.SpecialFunctions.Norm2
import SciLean.Analysis.SpecialFunctions.Pow
import SciLean.Analysis.SpecialFunctions.Trigonometric
import SciLean.Data.ArrayN
import SciLean.Data.ArraySet
import SciLean.Data.ArrayType
import SciLean.Data.ArrayType.Algebra
import SciLean.Data.ArrayType.Basic
import SciLean.Data.ArrayType.Notation
import SciLean.Data.ArrayType.Properties
import SciLean.Data.ColProd
import SciLean.Data.Curry
import SciLean.Data.DataArray
import SciLean.Data.DataArray.DataArray
import SciLean.Data.DataArray.Operations
import SciLean.Data.DataArray.PlainDataType
import SciLean.Data.DataArray.RevDeriv
import SciLean.Data.DataArray.VecN
import SciLean.Data.Function
import SciLean.Data.IndexType
import SciLean.Data.Int64
import SciLean.Data.ListN
import SciLean.Data.Prod
import SciLean.Data.Random
import SciLean.Data.StructType
import SciLean.Data.StructType.Algebra
import SciLean.Data.StructType.Basic
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
-- import SciLean.Geometry.Shape.TransfromedShape
-- import SciLean.Geometry.Shape.Triangle
import SciLean.Geometry.SurfaceParametrization
import SciLean.Lean.Array
import SciLean.Lean.Expr
import SciLean.Lean.HashMap
import SciLean.Lean.MergeMapDeclarationExtension
import SciLean.Lean.Meta.Basic
import SciLean.Lean.Meta.LiftLets
import SciLean.Lean.Meta.Replace
import SciLean.Lean.Meta.Structure
import SciLean.Lean.Name
import SciLean.Lean.String
import SciLean.Lean.ToSSA
import SciLean.Logic.Function.Bijective
import SciLean.Logic.Function.InvFun
import SciLean.Logic.Function.Preimage
import SciLean.Logic.Isomorph.Isomorph
import SciLean.Logic.Isomorph.IsomorphicType
import SciLean.Logic.Isomorph.RealToFloat.Basic
import SciLean.Logic.Isomorph.RealToFloat.Type
import SciLean.MeasureTheory.RnDeriv
import SciLean.MeasureTheory.WeakIntegral
-- import SciLean.Meta.DerivingAlgebra
-- import SciLean.Meta.DerivingOp
import SciLean.Meta.GenerateAddGroupHomSimp
import SciLean.Meta.GenerateFunProp
import SciLean.Meta.GenerateFunTrans
import SciLean.Meta.GenerateLinearMapSimp
import SciLean.Meta.Notation.Do
import SciLean.Meta.SimpAttr
import SciLean.Meta.SimpCore
import SciLean.Modules.DDG.SurfaceMesh
import SciLean.Modules.DDG.Trace
-- import SciLean.Modules.FiniteElement.Mesh.Circle
-- import SciLean.Modules.FiniteElement.Mesh.Line
-- import SciLean.Modules.FiniteElement.Mesh.Prism
-- import SciLean.Modules.FiniteElement.Mesh.PrismClosetsPoint
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
-- import SciLean.Modules.Geometry.Shape.TransfromedShape
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
-- import SciLean.Modules.Prob.SimpAttr
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
import SciLean.Probability.Distributions.Flip
import SciLean.Probability.Distributions.Normal
import SciLean.Probability.Distributions.Uniform
import SciLean.Probability.Distributions.WalkOnSpheres
import SciLean.Probability.IsAffineRandMap
import SciLean.Probability.PullMean
import SciLean.Probability.PushPullExpectation
import SciLean.Probability.Rand
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
import SciLean.Tactic.ConvIf
import SciLean.Tactic.ConvInduction
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
import SciLean.Tactic.MoveTerms
import SciLean.Tactic.OptimizeIndexAccess
import SciLean.Tactic.OptimizeIndexAccessInit
import SciLean.Tactic.PullLimitOut
import SciLean.Tactic.RefinedSimp
import SciLean.Tactic.StructuralInverse
import SciLean.Tactic.StructureDecomposition
import SciLean.Tactic.TimeTactic
import SciLean.Topology.Continuous
import SciLean.Util.Alternatives
import SciLean.Util.Approx.ApproxLimit
import SciLean.Util.Approx.ApproxSolution
import SciLean.Util.Approx.Basic
import SciLean.Util.DefOptimize
import SciLean.Util.Limit
import SciLean.Util.Profile
import SciLean.Util.RecVal
import SciLean.Util.RewriteBy
import SciLean.Util.SolveFun
import SciLean.Util.SorryProof
