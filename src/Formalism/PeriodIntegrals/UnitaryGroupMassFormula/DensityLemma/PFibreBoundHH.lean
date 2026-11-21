import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundVDefs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open scoped ENNReal NNReal

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

def UnipotentSetIsClosedSubgroup : Prop := ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → B2.IsClosedSubgroup (C2.N0set k r z)

end PI.UnitaryGroupMassFormula.DLm
