import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumCut
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StCutRestrLenExact
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StMixedTwistShift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplitFilt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutZeroNotLe
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TensorSubInsertion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

universe u w

theorem InterNumCut.proof (hF : CycleSplit.Filt.Statement.{u, w}) (hA : CutRestrLenExact.Statement.{u, w})
    (hB : MixedTwistShift.Statement.{u, w}) : InterNumCut.Statement.{u, w} :=
  _root_.UpperTheory.Reformulated.B.KleimanIntersectionNumberCut.proof hF hA hB

end

end GroundTheory.Heights₂.Heights.Kleiman
