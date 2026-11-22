import Mathlib
import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
import Formalism.LogSumExpBounds.CharacterSumPhase.NuclearNormBoundHolds
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CoefficientLeOperatorNorm
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
import Formalism.LatticeRigidity.StatementA
import Formalism.LatticeRigidity.StatementC
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd

namespace Formalism.IndefR.Eqv

open scoped ContDiff
open MeasureTheory

section Pt

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ev {k : ℕ} (j : Fin k) : Fin k → ℝ := Pi.single j 1

end Pt

end Formalism.IndefR.Eqv
