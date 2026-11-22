import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsSemipositiveRelTrivLine
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBoundedMul
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsCoordNeZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BirationalYPt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUpperNormalisation
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecMRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsSeparated
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallPacking
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepLocal
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepHomog
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSerreGraded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSpanStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionRingFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSectionsPower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsNonzero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSublatticeExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanningExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCovolumeLeGram
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGramContraction
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSublatticeDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSections
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.UnipotentCharacter

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SublatticeDegree.full : SublatticeDegree.Statement :=
  SublatticeDegree.proof SublatticeExtension.proof SpanningExtension.proof CovolumeLeGram.proof
    GramContraction.proof

theorem SuccessiveMinimaSpan.of_leaves (hC : KH.CondStatement) (hR : RelSectionsLarge.Statement) : SuccessiveMinimaSpan.Statement :=
  SuccessiveMinimaSpan.proof
    (SectionRingFinite.proof (SectionLatticeFinite.proof hC)
      (SectionSpanStep.proof (SpanStepHomog.proof (SpanStepLocal.proof (RelLatticeFinite.proof hR)))
        SerreGraded.proof))
    SectionBounded.proof SectionBoundedMul.proof

end GroundTheory.Heights₂.Heights.Targets
