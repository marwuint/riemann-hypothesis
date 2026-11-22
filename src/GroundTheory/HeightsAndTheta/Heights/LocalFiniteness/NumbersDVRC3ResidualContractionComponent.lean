import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelGrowthOffHypersurfacePolynomial
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.IsolatedPointsCount
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalLengthPlaces
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterDivSupp
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlacesRingQuot
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.DedekindZetaEqSumRealEisenstein
import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityHom
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.StatementsWitness
import GroundTheory.GlobalFields.AnalyticClassNumber.QuadraticLegendre
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarInj
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarUnit
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFunctionFieldFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionSupBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIndependentModBaseChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPrimeZariskiDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockStepLocal
import GroundTheory.HeightsAndTheta.Heights.Intersections.Imports
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartNormPts
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagArith
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagNeZero
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalCorresp
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalLift
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalStrict
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RingKrullDimLeOfIsAlgebraicAdjoinSingleton
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ResidualNewVarMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagProjTrdegLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingDimLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalCoeffRing
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotColon
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotRing

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.Inter_R1Indep : GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.of_remaining GroundTheory.Heights₂.Heights.AutoClose.Inter_R1RegMaxSurj

theorem GroundTheory.Heights₂.Heights.AutoClose.chart_norm_count : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.ChartNormCount.proof GroundTheory.Heights₂.Heights.AutoClose.Inter_ChartSpecCount GroundTheory.Heights₂.Heights.Inter.ChartNormPts.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarInj.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarInj.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarInj.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarNumerator

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarUnit.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarUnit.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarUnit.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarNumerator

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_FunctionFieldFinite.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.MChartDehomog.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartTrdeg

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocDim.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocDim.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocDim.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.MChartHomog.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartTrdeg GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartLocDim

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureModel : GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureModel.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureModel.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureTrdeg

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_FlagProjTrdegLe : GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureTrdeg

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ExceptionalContraction.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.ExceptionalContraction.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.ExceptionalContraction.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpHorizontalCorresp.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalCorresp.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalCorresp.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalSat.full GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpHorizontalMult GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalLift.full GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalStrict.full

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualContractionComponent.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.ResidualContractionComponent.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.ResidualContractionComponent.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalCoeffRing.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffRing.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffRing.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotRing.proof GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotPrimes.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocCycleLocalQuot GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotColon.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalQuotFinsum GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalCoeffLocal

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingDimLe.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingMem.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingIsLocal

theorem GroundTheory.Heights₂.Heights.AutoClose.TubeDeepAreaCount : GroundTheory.Heights₂.Heights.TubeDeepAreaCount.Statement :=
  @GroundTheory.Heights₂.Heights.TubeDeepAreaCount.proof GroundTheory.Heights₂.Heights.AutoClose.IsolatedPointsCount
