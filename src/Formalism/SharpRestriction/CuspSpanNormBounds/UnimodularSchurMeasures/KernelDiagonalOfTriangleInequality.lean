import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfAbsoluteConvergence
import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
import Formalism.LogSumExpBounds.CharacterSumPhase.NuclearNormBoundHolds
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CoefficientLeOperatorNorm
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
import Mathlib
import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
import Formalism.GelfandTransference.EnergyIdentity
import Formalism.NormUnitaryBounds.Statement
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShearCoefficients
import Formalism.NormUnitaryBounds.DetPolynomialWeights.LtSuccOfMemWeightCompositions
import Formalism.NormUnitaryBounds.DetPolynomialWeights.NormUnitary
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
import Formalism.LatticeTheta.ThetaShiftInversion
import Formalism.LatticeRigidity.StatementA
import Formalism.LatticeRigidity.StatementC
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
import Formalism.LatticeRigidity.StatementD

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set TopologicalSpace
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma
open Formalism.HermitianLatticeCounting.S7 (decExp)

def DistTri : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g k : Formalism.REAL.UJ ε), cartanDistance ε (g * k) ≤ cartanDistance ε g + cartanDistance ε k

end Formalism.MainNotions.LeviCoordinates

end
