import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PfAtZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFStep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFSecRed
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFVert
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFIntZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFHoriz
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreSum
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreBij
import GroundTheory.HeightsAndTheta.Heights.Intersections.EqZeroOfEventuallyEval
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRatioAlgDep
import GroundTheory.HeightsAndTheta.Heights.Intersections.MixedDiscEqZeroOfMulVec
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZIff
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZ
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsRest
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsIntegralLogNormRat
import GroundTheory.HeightsAndTheta.Heights.Intersections.PullWMemFibre
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsSheetPullW
import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjDeg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFnDegRelDeg
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForward
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.NumericalSegre
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.NumbersDVRC3ResidualContractionComponent
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.FibreDim
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocMaxIdeals
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueDeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueFibreDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueAdjoin
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueFrac

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter

theorem projDeg_all :
    ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)],
      ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι' := by
  intro F _ K _ ι _ K' _ ι' _
  exact GroundTheory.Heights₂.Heights.Targets.ProjDeg.of_found
    (GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.of_divPushForward
      (GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.proof
        GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe.proof
        GroundTheory.Heights₂.Heights.NumbersDVR.DivPushForwardLocalZero))
    GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg.proof F ι ι'

theorem semilocMaxIdeals_of_fibreIncomp (hFI : FibreIncomp.Statement) : SemilocMaxIdeals.Statement :=
  SemilocMaxIdeals.proof (FibreOverFinite.proof hFI) hFI SemilocIntegral.full LocRingDimOne.full

theorem semilocResidueDeg_of_fibreIncomp (hFI : FibreIncomp.Statement) (hFD : FibreDimStatement) :
    SemilocResidueDeg.Statement :=
  SemilocResidueDeg.proof (SemilocResidueFibreDim.proof (FibreDivSupp.proof hFI) hFD FibreDimensionZero.full)
    (SemilocResidueAdjoin.proof
      (SemilocResidueFrac.proof SemilocFinite.full (semilocMaxIdeals_of_fibreIncomp hFI))
      ChartScalingIndep.full)

end GroundTheory.Heights₂.Heights.ForSecondHalf
