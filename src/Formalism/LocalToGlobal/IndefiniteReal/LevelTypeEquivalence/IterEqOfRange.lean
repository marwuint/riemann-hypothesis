import Mathlib
import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
import Formalism.LogSumExpBounds.CharacterSumPhase.NuclearNormBoundHolds
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CoefficientLeOperatorNorm
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
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

namespace Formalism.IndefR.Eqv

open scoped ContDiff
open MeasureTheory

section Pt

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ev {k : ℕ} (j : Fin k) : Fin k → ℝ := Pi.single j 1

end Pt

end Formalism.IndefR.Eqv
