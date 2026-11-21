import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeBoundInBanachSpace
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.UnipotentFixesFrameVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnitaryWeylCompact

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

lemma gN_cont (k r : ℕ) : Continuous (fun g : B.Mat k r => B.gN g) := by
  unfold B.gN
  fun_prop

end PI.UnitaryGroupMassFormula.DLm
