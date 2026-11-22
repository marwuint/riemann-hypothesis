import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.RegularizedMaxC2ExampleRealLine
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.ConvergenceRate
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Telescoping
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PPolyMaxLowerBound
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncPsh
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncTransfer
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBoundingKaehler
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TendstoLocallyUniformlyOnOfNhds
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassZero
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.SystemIndependence
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListTailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TailDimZero
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UniformIntegrability
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPushDown

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open GroundTheory.Heights₂.Heights.LowerBoundFree

theorem BoundingKaehler.full : BoundingKaehler.Statement := BoundingKaehler.proof

theorem GreenMassZero.full : GreenMassZero.Statement := GreenMassZero.proof

theorem UniformIntegrability.of_greenMass (h₁ : GreenMassStep.Statement)
    (h₂ : GreenMassReplace.Statement) (h₃ : GreenMassError.Statement) :
    UniformIntegrability.Statement :=
  UniformIntegrability.proof GreenMassZero.full h₁ h₂ h₃

end GroundTheory.Heights₂.Heights.AnalyticLimit
