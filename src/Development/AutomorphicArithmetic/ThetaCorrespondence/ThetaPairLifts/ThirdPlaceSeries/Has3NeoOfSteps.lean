import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiedDataReciprocity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKerTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPlacesRayField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TiedSKAtWitnesses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHostDatumOfPlaceData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevExOfOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTiedOfLevEx
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WitnessesPassAlongSetDivision
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsEOfHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZetaUniformOfExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelectedRealization
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedRealizationGeometric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftGroupFormsEqExtendedRationalFormsCompanion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsRowOfEigensystemIndexGoodCharactersStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodGenericCharacterOfSeriesTypesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamPOfPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedLowerMapHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedSideRealizationHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRationalRows
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisAveragedSeriesOfClassSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullRankThetaSeriesFormsOfRationalScalars
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorPreservesSupLatticeRealSide
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesRationalityAndCoefficientBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistOfCuspParams
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Lv3StageMovesSpectral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PublishedInputsImplyConclusion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PositionStageMovesGeometric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendsFineAdelicDatumToLargerFieldOfHyp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsFromPrintedInputs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondBoundOfPrimitive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesCoverOfPrimitive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RhoStabChiInLL0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCAtState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelCharacterEqProdSuperdiagonalSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHeckeAtZeroOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemOfListProdMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowEigMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StableHeckeLevelCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClassMapCorrespondence
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeComponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentStarCompatibleOfLabellingAgree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameParameterCoupled
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateVectorInSubspace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabFixedOfTypesTrue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InfinitesimalCharacterReference
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionToLocalLanglandsA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionSeriesB0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StateB2OfRationalData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesAtThetaTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Detects
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSumLeOfLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeUnitOfExportTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientIntegralFramedPointCompleteField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeometricAllStates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseFrobSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteExceptionalPlacesOverPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyLocalGlobal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteSplittingSetFrobeniusPolynomials
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenRationality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOutIffGenAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenConductor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteChosenSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleResidualPointDescendsCoefficientExten
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefRingTakenOfLocalisationCoefficientExte
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneOfCoefRingTakenAtLiveLocalisations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneTypePrimeOfCoefRingTakenAtLive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLocusDecomposesOverCoefRingOfChebotarev
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceLengthTwistedPlacesOfHeckeIntegrality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceInnerProductClassSumRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplitAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisRepsCuspidalAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitenessOfHyp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsPositiveScalarsWithoutCongruenceLengths
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankIsotEqIsotL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoeffInvEqCoeff
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteLevelAndSecond
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.SRe
set_option maxHeartbeats 2000000
namespace GlobalTheory.Mem.Top.Bl
theorem has3_neo_of_localLanglands_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (hB : ExistsUnlocalizedSaturatedState) (hA : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevelExists hL) (hMt : SMt) (hRat : _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL)
    (hCu : _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL) (hB0 : _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep) (hB1 : _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep) (hB2 : _root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep) (hC : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL) (hFin : _root_.GlobalTheory.HeightCounting.Up.SpectralFiniteness hL cDep)
    (S : SExt) (Γ : GeoP) : StepW Start (Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s) := by
  have h := StepW.and hB (hA.and (hMt.and (hRat.and (hCu.and (hB0.and (hB1.and (hB2.and (hC.and hFin))))))))
  refine h.trans (StepW.of_all ?_)
  intro K B f T w _ _ H
  obtain ⟨⟨P, x, sat, hLoc, -⟩, a, mt, rat, cu, b0, b1, b2, c, fin⟩ := H
  obtain ⟨x1, ⟨la⟩, -⟩ := a P x hLoc
  obtain ⟨imt⟩ := mt P x1
  obtain ⟨irat⟩ := rat P x1 la
  have li : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x1 := { toLA := la, mt := imt, rat := irat, cusp := cu P x1 la }
  obtain ⟨x2, ⟨l0⟩, p2⟩ := b0 P x1 li
  obtain ⟨x3, ⟨l1⟩, p3⟩ := b1 P x2 l0
  obtain ⟨x4, ⟨l2⟩, p4⟩ := b2 P x3 l1
  obtain ⟨sc⟩ := c P x4 l2
  obtain ⟨Z, v, -, -⟩ := fin P x4 { toStrictHenselianAcyclic := l2, c := sc } S Γ ⟨p4 (p3 p2), sat⟩
  exact ⟨Z, ⟨v⟩⟩
end GlobalTheory.Mem.Top.Bl
end
