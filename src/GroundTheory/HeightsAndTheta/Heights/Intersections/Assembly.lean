import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBridge
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.AevalNeZeroOfNotMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZIff
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTer
import GroundTheory.HeightsAndTheta.Heights.Intersections.LiftZComponent
import GroundTheory.HeightsAndTheta.Heights.Intersections.AevalMemAdjoin
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsNormalise
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMore
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogProdInt
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurther
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogOfPullWeight
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsRest
import GroundTheory.HeightsAndTheta.Heights.Intersections.ChartCongr
import GroundTheory.HeightsAndTheta.Heights.Intersections.PAdjoinIndepRelfinrank
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBCMult
import GroundTheory.HeightsAndTheta.Heights.Intersections.PWWArithVar
import GroundTheory.HeightsAndTheta.Heights.Intersections.PCentreOverW
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartScalingIndep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChoice
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDeLeSemiPos
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDeSlotAdd
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagDiv
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagFormDiv
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOrdOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagPull
import GroundTheory.HeightsAndTheta.Heights.Intersections.PEvalKerKrullDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreDivSupp
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreOverFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFinrankAdjoinRange
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.LinEmbedSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagMinorsTrdeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagPivotAlgIndep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagPivotIdentity
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFnDegAdjoin
import GroundTheory.HeightsAndTheta.Heights.Intersections.PIntClosureLocFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.LinEmbedAlg
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsHomogeneousOfIsMultiHomogOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLinearQuotient
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingChartLoc
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingDimOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingInj
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingIntClosure
import GroundTheory.HeightsAndTheta.Heights.Intersections.POrbitCompNonvanish
import GroundTheory.HeightsAndTheta.Heights.Intersections.PfAtZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreBij
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreMult
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFHoriz
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFSecRed
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFStep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFVert
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterResExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushA
import GroundTheory.HeightsAndTheta.Heights.Intersections.DeEqZeroOfSemiPosOff
import GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleFibre
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsMeasurable
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAddFirst
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsMonoSemiPos
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsRegLimit
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.FunFieldLeLocRing
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProofOfNoethPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.LogNormDivSameOrbit
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisMore
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisFurther
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisExtra
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisRest
import GroundTheory.HeightsAndTheta.Heights.Intersections.OrderOfIntegral
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisSide
import GroundTheory.HeightsAndTheta.Heights.Intersections.KerIsMultiHomogIdeal
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisTail
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisLast
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArIntMul
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRankAdjoinFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRankFracDegree
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRelAlgClosureFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.JacMinorC
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocChartRatio
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocIntegral
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocLength
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocLengthSum
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocRank
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocRankAdjoin
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocRankFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIExists
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIMultilin
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmISymm
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIUnique
import GroundTheory.HeightsAndTheta.Heights.Intersections.PValCentreZ
import GroundTheory.HeightsAndTheta.Heights.Intersections.PWellDefined
import GroundTheory.HeightsAndTheta.Heights.Intersections.PZeroSetNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ArithSystem
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.BaseChangeMinimal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Contract
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixed
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixedField
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GeoNum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Multilin
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCoordFibreDeg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCoordRatioDeg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFCoord
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreMultiHomog
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGenFibreChartDeg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSymmRelabel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjContract

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

theorem RegularityFunctionFieldNumber.full : GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.proof

theorem RegularityDivisorSupportClosed.full : GroundTheory.Heights₂.Heights.Inter.RegularityDivisorSupportClosed.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityDivisorSupportClosed.proof

theorem LocRingPow.full : GroundTheory.Heights₂.Heights.Inter.LocRingPow.Statement := GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.LocRingPow

theorem RegularityDenominator.full : GroundTheory.Heights₂.Heights.Inter.RegularityDenominator.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityDenominator.proof GroundTheory.Heights₂.Heights.Inter.RegularityDivisorSupportClosed.full GroundTheory.Heights₂.Heights.Inter.LocRingPow.full

theorem RegularityValuationCentre.full : GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre.proof

theorem RegularityRelativeClosedPoint.full : GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint.proof

theorem RegularityIntegral.full : GroundTheory.Heights₂.Heights.Inter.RegularityIntegral.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityIntegral.proof GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre.full GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint.full

theorem RegularityOrder.full : GroundTheory.Heights₂.Heights.Inter.RegularityOrder.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityOrder.proof GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.full GroundTheory.Heights₂.Heights.Inter.RegularityDenominator.full GroundTheory.Heights₂.Heights.Inter.RegularityIntegral.full

theorem RegularityLocalPrime.full : GroundTheory.Heights₂.Heights.Inter.RegularityLocalPrime.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityLocalPrime.proof GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full

theorem RegularityLocalize.full : GroundTheory.Heights₂.Heights.Inter.RegularityLocalize.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityLocalize.proof GroundTheory.Heights₂.Heights.Inter.RegularityLocalPrime.full

theorem regularityLocalDimension_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityLocalDimension_holds.Statement := GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.regularityLocalDimension_holds

theorem RegularityLocalFinite.full : GroundTheory.Heights₂.Heights.Inter.RegularityLocalFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityLocalFinite.proof GroundTheory.Heights₂.Heights.Inter.regularityLocalDimension_holds.full

theorem LocRingNoeth.full : GroundTheory.Heights₂.Heights.Inter.LocRingNoeth.Statement := GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.LocRingNoeth

theorem pointForm_holds.full : GroundTheory.Heights₂.Heights.Inter.pointForm_holds.Statement :=
  GroundTheory.Heights₂.Heights.Targets.Contract.pulledBackForms_topDensity_vanish

theorem PullbackEliminationOfVariable.full : GroundTheory.Heights₂.Heights.Inter.PullbackEliminationOfVariable.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PullbackEliminationOfVariable.proof

theorem PullbackVanishingOfNullCycle.full : GroundTheory.Heights₂.Heights.Inter.PullbackVanishingOfNullCycle.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PullbackVanishingOfNullCycle.proof GroundTheory.Heights₂.Heights.Inter.PullbackEliminationOfVariable.full

theorem RankAdjoinFrac.full : GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac.proof

theorem regularityEmbedding_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds.proof

theorem ProjectivePointVertical.full : GroundTheory.Heights₂.Heights.Inter.ProjectivePointVertical.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ProjectivePointVertical.proof (by intros; exact GroundTheory.Heights₂.Heights.geoNumStatement _) (by intros; exact GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full _ _) (by intros; exact GroundTheory.Heights₂.Heights.Targets.ProjContract.full _ _ _ _ _)

theorem PushforwardProjectivePoint.full : GroundTheory.Heights₂.Heights.Inter.PushforwardProjectivePoint.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PushforwardProjectivePoint.proof GroundTheory.Heights₂.Heights.imageArith GroundTheory.Heights₂.Heights.Inter.pointForm_holds.full GroundTheory.Heights₂.Heights.Inter.ProjectivePointVertical.full

theorem ArithmeticIntersectionHorizontal.full : GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal.proof ReciprocityTheory.ChartRestriction.G.Geo.divSuppArith GroundTheory.Heights₂.Heights.imageArith GroundTheory.Heights₂.Heights.Inter.PushforwardProjectivePoint.full

theorem ArithmeticIntersectionFibreMultiHomogeneous.full : GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionFibreMultiHomogeneous.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionFibreMultiHomogeneous.proof

theorem EvalKerKrullDim.full : GroundTheory.Heights₂.Heights.Inter.EvalKerKrullDim.Statement :=
  GroundTheory.Heights₂.Heights.Inter.EvalKerKrullDim.proof

theorem FibreTranscendenceDegreeAlt.full : GroundTheory.Heights₂.Heights.Inter.FibreTranscendenceDegreeAlt.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreTranscendenceDegreeAlt.proof GroundTheory.Heights₂.Heights.Inter.EvalKerKrullDim.full

theorem FibreDimensionZero.full : GroundTheory.Heights₂.Heights.Inter.FibreDimensionZero.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreDimensionZero.proof GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionFibreMultiHomogeneous.full GroundTheory.Heights₂.Heights.Inter.EvalKerKrullDim.full GroundTheory.Heights₂.Heights.Inter.FibreTranscendenceDegreeAlt.full

theorem ChartRankAdjoin.full : GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.Statement := GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.ChartRankAdjoin

theorem FnDegAdjoin.full : GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin.proof

theorem ChartScalingIndep.full : GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.proof

theorem AdjoinIndepRelfinrank.full : GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.Statement :=
  GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.proof

theorem FinrankAdjoinRange.full : GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.proof

theorem VerticalDegreeAfterAdjoining.full : GroundTheory.Heights₂.Heights.Inter.VerticalDegreeAfterAdjoining.Statement :=
  GroundTheory.Heights₂.Heights.Inter.VerticalDegreeAfterAdjoining.proof GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac.full GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin.full GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.full GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.full GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.full

theorem VerticalDegree.full : GroundTheory.Heights₂.Heights.Inter.VerticalDegree.Statement :=
  GroundTheory.Heights₂.Heights.Inter.VerticalDegree.proof GroundTheory.Heights₂.Heights.Inter.FibreDimensionZero.full GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.full GroundTheory.Heights₂.Heights.Inter.VerticalDegreeAfterAdjoining.full

theorem ValCentreZ.full : GroundTheory.Heights₂.Heights.Inter.ValCentreZ.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ValCentreZ.proof

theorem CentreOverW.full : GroundTheory.Heights₂.Heights.Inter.CentreOverW.Statement :=
  GroundTheory.Heights₂.Heights.Inter.CentreOverW.proof

theorem SemilocIntegral.full : GroundTheory.Heights₂.Heights.Inter.SemilocIntegral.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocIntegral.proof GroundTheory.Heights₂.Heights.Inter.ValCentreZ.full GroundTheory.Heights₂.Heights.Inter.CentreOverW.full

theorem LocRingChartLoc.full : GroundTheory.Heights₂.Heights.Inter.LocRingChartLoc.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingChartLoc.proof

theorem RelAlgClosureFinite.full : GroundTheory.Heights₂.Heights.Inter.RelAlgClosureFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RelAlgClosureFinite.proof

theorem IntClosureLocFinite.full : GroundTheory.Heights₂.Heights.Inter.IntClosureLocFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.IntClosureLocFinite.proof GroundTheory.Heights₂.Heights.Inter.RelAlgClosureFinite.full

theorem LocRingIntClosureFinite.full : GroundTheory.Heights₂.Heights.Inter.LocRingIntClosureFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingIntClosureFinite.proof GroundTheory.Heights₂.Heights.Inter.LocRingChartLoc.full GroundTheory.Heights₂.Heights.Inter.IntClosureLocFinite.full

theorem LocRingFrac.full : GroundTheory.Heights₂.Heights.Inter.LocRingFrac.Statement := GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.LocRingFrac

theorem LocRingLocal.full : GroundTheory.Heights₂.Heights.Inter.LocRingLocal.Statement := GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.LocRingLocal

theorem LocRingDimOne.full : GroundTheory.Heights₂.Heights.Inter.LocRingDimOne.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingDimOne.proof GroundTheory.Heights₂.Heights.Inter.LocRingFrac.full GroundTheory.Heights₂.Heights.Inter.LocRingNoeth.full GroundTheory.Heights₂.Heights.Inter.LocRingLocal.full GroundTheory.Heights₂.Heights.Inter.LocRingPow.full

theorem SemilocFinite.full : GroundTheory.Heights₂.Heights.Inter.SemilocFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocFinite.proof GroundTheory.Heights₂.Heights.Inter.SemilocIntegral.full GroundTheory.Heights₂.Heights.Inter.LocRingIntClosureFinite.full GroundTheory.Heights₂.Heights.Inter.LocRingDimOne.full

theorem LocRingInj.full : GroundTheory.Heights₂.Heights.Inter.LocRingInj.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingInj.proof

theorem regularityDehomogenization_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.Statement := GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.regularityDehomogenization_holds

theorem GenericPointExists.full : GroundTheory.Heights₂.Heights.Inter.GenericPointExists.Statement :=
  GroundTheory.Heights₂.Heights.Inter.GenericPointExists.proof

theorem ThmIUnique.full : GroundTheory.Heights₂.Heights.Inter.ThmIUnique.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ThmIUnique.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero

theorem ArithmeticIntersectionChartFinite.full : GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionChartFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionChartFinite.proof

theorem pullbackBadImage_holds.full : GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds.proof

theorem regularityLocalCardinality_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityLocalCardinality_holds.Statement := GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.regularityLocalCardinality_holds

theorem pullbackPushforward_holds.full : GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.Statement := GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.pullbackPushforward_holds

theorem SemiPosTwist.full : GroundTheory.Heights₂.Heights.Inter.SemiPosTwist.Statement := GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.SemiPosTwist

theorem RankFracDegree.full : GroundTheory.Heights₂.Heights.Inter.RankFracDegree.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RankFracDegree.proof

theorem regularityPointsSum_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityPointsSum_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityPointsSum_holds.proof

theorem HorizNotMem.full : GroundTheory.Heights₂.Heights.Inter.HorizNotMem.Statement :=
  GroundTheory.Heights₂.Heights.Inter.HorizNotMem.proof

theorem SheetHessPSD.full : GroundTheory.Heights₂.Heights.Inter.SheetHessPSD.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SheetHessPSD.proof

theorem RegCurvBound.full : GroundTheory.Heights₂.Heights.Inter.RegCurvBound.Statement := GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.RegCurvBound

theorem OrbitCompNonvanish.full : GroundTheory.Heights₂.Heights.Inter.OrbitCompNonvanish.Statement :=
  GroundTheory.Heights₂.Heights.Inter.OrbitCompNonvanish.proof

theorem pullbackDensity_holds.full : GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds.proof

theorem Closed.ReciprocityTheory.ChartRestriction.G.AI.I2.Unique : ReciprocityTheory.ChartRestriction.G.AI.I2.UniqueStatement :=
  GroundTheory.Heights₂.Heights.Inter.ThmIUnique.full

theorem Closed.Targets.GenFibreChartDeg : GroundTheory.Heights₂.Heights.Targets.GenFibreChartDeg.Statement :=
  GroundTheory.Heights₂.Heights.Targets.GenFibreChartDeg.proof GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.full GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.full

theorem Closed.Targets.CoordFibreDeg : GroundTheory.Heights₂.Heights.Targets.CoordFibreDeg.Statement :=
  GroundTheory.Heights₂.Heights.Targets.CoordFibreDeg.proof GroundTheory.Heights₂.Heights.Targets.FibreMultiHomog.proof GroundTheory.Heights₂.Heights.Inter.Closed.Targets.GenFibreChartDeg GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg.proof

theorem ArithmeticIntersectionVertical.of_remaining
    (hProjDeg : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [(k : K) → Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [(k : K') → Fintype (ι' k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι') :
    GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionVertical.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionVertical.proof (by intros; exact GroundTheory.Heights₂.Heights.geoNumStatement _) (by intros; exact GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full _ _) (by intros; exact GroundTheory.Heights₂.Heights.Targets.ProjContract.full _ _ _ _ _) hProjDeg GroundTheory.Heights₂.Heights.Inter.VerticalDegree.full

theorem FibreOverFinite.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement) :
    GroundTheory.Heights₂.Heights.Inter.FibreOverFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreOverFinite.proof hFibreIncomp

theorem SemilocChartRatio.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocChartRatio.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocChartRatio.proof (GroundTheory.Heights₂.Heights.Inter.FibreOverFinite.of_remaining hFibreIncomp)

theorem SemilocRankFrac.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac.proof GroundTheory.Heights₂.Heights.Inter.RankFracDegree.full GroundTheory.Heights₂.Heights.Inter.SemilocFinite.full (GroundTheory.Heights₂.Heights.Inter.SemilocChartRatio.of_remaining hFibreIncomp)

theorem SemilocRankAdjoin.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocRankAdjoin.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocRankAdjoin.proof (GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac.of_remaining hFibreIncomp) GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.full

theorem SemilocRank.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocRank.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocRank.proof hFibreDim (GroundTheory.Heights₂.Heights.Inter.SemilocRankAdjoin.of_remaining hFibreIncomp)

theorem FibreDivSupp.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement) :
    GroundTheory.Heights₂.Heights.Inter.FibreDivSupp.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreDivSupp.proof hFibreIncomp

theorem SemilocLengthSum.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocLengthSum.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocLengthSum.proof GroundTheory.Heights₂.Heights.Inter.SemilocFinite.full hSemilocMaxIdeals hSemilocResidueDeg (GroundTheory.Heights₂.Heights.Inter.FibreDivSupp.of_remaining hFibreIncomp) GroundTheory.Heights₂.Heights.Inter.LocRingDimOne.full (GroundTheory.Heights₂.Heights.Inter.FibreOverFinite.of_remaining hFibreIncomp)

theorem SemilocLength.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocLength.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocLength.proof (GroundTheory.Heights₂.Heights.Inter.SemilocLengthSum.of_remaining hFibreIncomp hSemilocMaxIdeals hSemilocResidueDeg) (GroundTheory.Heights₂.Heights.Inter.FibreDivSupp.of_remaining hFibreIncomp) GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.full

theorem ArithmeticIntersectionDivisorPushforward.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionDivisorPushforward.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionDivisorPushforward.proof GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.full GroundTheory.Heights₂.Heights.Inter.LocRingDimOne.full GroundTheory.Heights₂.Heights.Inter.SemilocFinite.full (GroundTheory.Heights₂.Heights.Inter.SemilocRank.of_remaining hFibreIncomp hFibreDim) (GroundTheory.Heights₂.Heights.Inter.SemilocLength.of_remaining hFibreIncomp hSemilocMaxIdeals hSemilocResidueDeg)

theorem ArithmeticIntersectionCycle.of_remaining
    (hProjDeg : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [(k : K) → Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [(k : K') → Fintype (ι' k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι')
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionCycle.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionCycle.proof GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal.full (GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionVertical.of_remaining hProjDeg) (GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionDivisorPushforward.of_remaining hFibreIncomp hSemilocMaxIdeals hSemilocResidueDeg hFibreDim) GroundTheory.Heights₂.Heights.Inter.GenericPointExists.full (by intros; exact GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full _ _)

theorem GenericPointsInAffineChart.of_remaining
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement) :
    GroundTheory.Heights₂.Heights.Inter.GenericPointsInAffineChart.Statement :=
  GroundTheory.Heights₂.Heights.Inter.GenericPointsInAffineChart.proof GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionChartFinite.full hAI3ChartNormCount GroundTheory.Heights₂.Heights.Inter.OrbitCompNonvanish.full

theorem GenericPointsAvoidBadLocus.of_remaining
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement) :
    GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.Statement :=
  GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.proof (GroundTheory.Heights₂.Heights.Inter.GenericPointsInAffineChart.of_remaining hAI3ChartNormCount)

theorem GenericPointsCount.of_remaining
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement) :
    GroundTheory.Heights₂.Heights.Inter.GenericPointsCount.Statement :=
  GroundTheory.Heights₂.Heights.Inter.GenericPointsCount.proof (GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.of_remaining hAI3ChartNormCount)

theorem PullbackDegreeCount.of_remaining
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount.proof hFibreDim GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.full (GroundTheory.Heights₂.Heights.Inter.GenericPointsCount.of_remaining hAI3ChartNormCount) GroundTheory.Heights₂.Heights.Inter.PullbackVanishingOfNullCycle.full GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds.full

theorem RegularityMaximalSpectrum.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSpectrum.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSpectrum.proof GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full GroundTheory.Heights₂.Heights.Inter.RegularityLocalize.full GroundTheory.Heights₂.Heights.Inter.LocRingInj.full hR1RegMaxSurj

theorem RegularityLocal.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityLocal.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityLocal.proof GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full (GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSpectrum.of_remaining hR1RegMaxSurj)

theorem RegularityFormula.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityFormula.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityFormula.proof GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.full GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full (GroundTheory.Heights₂.Heights.Inter.RegularityLocal.of_remaining hR1RegMaxSurj)

theorem RegularityLocalProduct.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityLocalProduct.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityLocalProduct.proof GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.full (GroundTheory.Heights₂.Heights.Inter.RegularityFormula.of_remaining hR1RegMaxSurj) GroundTheory.Heights₂.Heights.Inter.RegularityDenominator.full GroundTheory.Heights₂.Heights.Inter.RegularityDivisorSupportClosed.full GroundTheory.Heights₂.Heights.Inter.RegularityLocalFinite.full

theorem VerticalEmbedding.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.VerticalEmbedding.Statement :=
  GroundTheory.Heights₂.Heights.Inter.VerticalEmbedding.proof GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.full GroundTheory.Heights₂.Heights.Inter.regularityLocalCardinality_holds.full (GroundTheory.Heights₂.Heights.Inter.RegularityLocalProduct.of_remaining hR1RegMaxSurj)

theorem VerticalClosedPoints.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.VerticalClosedPoints.Statement :=
  GroundTheory.Heights₂.Heights.Inter.VerticalClosedPoints.proof GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds.full (GroundTheory.Heights₂.Heights.Inter.VerticalEmbedding.of_remaining hR1RegMaxSurj)

theorem RPositionAdd.of_remaining
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.RPositionAdd.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RPositionAdd.proof ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite hPtsIntegrable

theorem PtsMonoSemiPos.of_remaining
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.PtsMonoSemiPos.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PtsMonoSemiPos.proof hPtsIntegrable GroundTheory.Heights₂.Heights.Inter.SheetHessPSD.full

theorem RegularityProductFormula.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityProductFormula.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityProductFormula.proof GroundTheory.Heights₂.Heights.Inter.regularityPointsSum_holds.full (GroundTheory.Heights₂.Heights.Inter.VerticalClosedPoints.of_remaining hR1RegMaxSurj)

theorem RegularityIndependence.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite (GroundTheory.Heights₂.Heights.Inter.RegularityProductFormula.of_remaining hR1RegMaxSurj)

end GroundTheory.Heights₂.Heights.Inter
