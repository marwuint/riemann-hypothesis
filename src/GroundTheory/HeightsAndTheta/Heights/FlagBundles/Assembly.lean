import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
import GroundTheory.PAdicHodge.SlopeCauchyBinet
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PDiagonalQuotient
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGKernelIdentity
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereHeightUniform
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalKernel
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereLongitudeCoordinates
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalHeightReduction
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalKernelPairing
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalBilinearFormula
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGHatIdentity
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibreConstantClosedForm
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibreIntegralInvariant
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyIntegral

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

theorem GKernelIdentity.full : GKernelIdentity.Statement := GroundTheory.Heights₂.Heights.FlagBundles.GKernelIdentity.proof

theorem ZonalKernel.full : ZonalKernel.Statement := GroundTheory.Heights₂.Heights.FlagBundles.ZonalKernel.proof

theorem SphereLongitudeCoordinates.full : SphereLongitudeCoordinates.Statement := GroundTheory.Heights₂.Heights.FlagBundles.SphereLongitudeCoordinates.proof

theorem ZonalHeightReduction.full : ZonalHeightReduction.Statement :=
  ZonalHeightReduction.proof SphereLongitudeCoordinates.full ZonalKernel.full

theorem ZonalKernelPairing.full : ZonalKernelPairing.Statement :=
  ZonalKernelPairing.proof

theorem ZonalBilinearFormula.full : ZonalBilinearFormula.Statement :=
  ZonalBilinearFormula.proof ZonalHeightReduction.full ZonalKernelPairing.full

theorem GHatIdentity.full : GHatIdentity.Statement :=
  GHatIdentity.proof GKernelIdentity.full

theorem FibreConstantClosedForm.full : FibreConstantClosedForm.Statement :=
  FibreConstantClosedForm.proof ZonalBilinearFormula.full GHatIdentity.full

theorem fibreConstant_eq (k : ℕ) :
    fibreConstant k = -(1 / 2) * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1) :=
  FibreConstantClosedForm.full.1 k

theorem FibreIntegralInvariant.full : FibreIntegralInvariant.Statement :=
  FibreIntegralInvariant.proof FibreConstantClosedForm.full

end GroundTheory.Heights₂.Heights.FlagBundles
