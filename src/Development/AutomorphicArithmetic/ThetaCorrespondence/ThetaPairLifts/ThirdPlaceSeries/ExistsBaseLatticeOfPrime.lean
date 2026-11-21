import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeightSetResidueCharacteristic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
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
import Formalism.LocalToGlobal.UnitaryNorms.DatumS
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.IndefiniteReal.IsFDiagIffDiagonal
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedRealizationGeometric
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftGroupFormsEqExtendedRationalFormsCompanion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsRowOfEigensystemIndexGoodCharactersStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodGenericCharacterOfSeriesTypesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamPOfPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypesViaFullHeckeAlgebraEigensystemsStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OverIx
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFamilyLabelContainingFiniteTypePartsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexSpanRationalLiftFormsEqBasePartStatement
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedLowerMapHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedSideRealizationHolds
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnramifiedNoJump
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumThEmptyNeZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistAllPowersOfGaloisCohomologyClassField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmbientBaseHeq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRationalRows
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisAveragedSeriesOfClassSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullRankThetaSeriesFormsOfRationalScalars
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceIndexMemFirstPairOfCompatibleChoice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorPreservesSupLatticeRealSide
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesRationalityAndCoefficientBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistOfCuspParams
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Lv3StageMovesSpectral
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PublishedInputsImplyConclusion
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.PeriodIntegrals.BesselMapUniq
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PositionStageMovesGeometric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendsFineAdelicDatumToLargerFieldOfHyp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsFromPrintedInputs
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondBoundOfPrimitive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesCoverOfPrimitive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RhoStabChiInLL0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCAtState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelCharacterEqProdSuperdiagonalSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHeckeAtZeroOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemOfListProdMem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfFirstStepLoc
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsIsHeckeSetting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepSplittingCharactersTameLevelResidue
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowEigMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StableHeckeLevelCharacter
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClassMapCorrespondence
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeComponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentStarCompatibleOfLabellingAgree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameParameterCoupled
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateVectorInSubspace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabFixedOfTypesTrue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InfinitesimalCharacterReference
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionToLocalLanglandsA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionSeriesB0
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StateB2OfRationalData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataLaterStagesWithNewTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedReadingTransportedNewTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesAtThetaTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Detects
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSumLeOfLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeUnitOfExportTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientIntegralFramedPointCompleteField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitHeckePrimeOffLevelOfHeckeIndexPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeometricAllStates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFactsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseFrobSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteExceptionalPlacesOverPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyLocalGlobal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteSplittingSetFrobeniusPolynomials
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenRationality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContainsAfterLocalization
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOutIffGenAt
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffMonicPolySum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexHeckeEigenvectorDescendsToCoefficientFiel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenConductor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteChosenSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleResidualPointDescendsCoefficientExten
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefRingTakenOfLocalisationCoefficientExte
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneOfCoefRingTakenAtLiveLocalisations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneTypePrimeOfCoefRingTakenAtLive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLocusDecomposesOverCoefRingOfChebotarev
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceLengthTwistedPlacesOfHeckeIntegrality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceInnerProductClassSumRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndicesPairingLengthsVanishOffTwistedPlaces
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplitAll
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisRepsCuspidalAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitenessOfHyp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodRowCuspParam
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterLawsEmpty
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterUnramifiedInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicRealNonzero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalInertiaOfIsotypic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InfinityTypeOfLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowLocalAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecT
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOfLocalLanglands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsPositiveScalarsWithoutCongruenceLengths
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankIsotEqIsotL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoeffInvEqCoeff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodTypesOfTypesTrue
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLevelTypeFormsOfUniversalCoeffReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteLevelAndSecond
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultQ
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AllStagesAtMemberOfSpecializations
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FiniteLevelAndSecond
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Has3NeoOfSteps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OrgOfKeptStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SlotMvPrmRNelStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutomorphyOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberEClosing
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExBLIsLinkedPrmRStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.SRe
set_option maxHeartbeats 2000000
namespace GlobalTheory.Mem.Top.Bl
theorem exists_baseLattice_of_pair_alt (hA : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt) (hE : _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis) (hH : _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hN : _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL) (N Ng : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL)
    (toB : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c))
    (toN : ∀ K B f T w Z Wt p0 t nch n xd c, Ng K B f T w Z Wt p0 t nch n xd c →
      Nonempty (N K B f T w Z Wt p0 t nch n xd c) ∧ GoodO (w.D Z) nch xd)
    (has3 : StepW Start (Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s))
    (lv : LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) (lvg : LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)).s)
    (intersection_update_fsHerm_neg_one : PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s)
    (second : Pass KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) fun K B f T =>
      ∃ w : ColW B f T, Start K B f T w ∧ Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)).s K B f T w)
    (hMQ : _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry))) :
    MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s ∧
      GlobalTheory.Fc.ExBL KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s)
        (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry))) := by
  have exp := _root_.GlobalTheory.T.automorphy_of_hypotheses_alt_alt hE.e1 hE.e2 hE.e3 hE.e4 hE.e5 hE.e6 hE.e7 hE.e8 hE.e9 hE.e10 hE.e11 hE.e12 hE.e13 hA.a6 hE.e14 hA.a22
    hE.e15 hE.e16 hE.e17 hE.e18 hE.e19 hE.e20 hE.e21 hE.e22 hE.e23 hE.e24 hE.e25 hN.pr hN.ser hL hN.parMem N
    SExt.none (geoCl anyGeometry) toB
  refine ⟨?_, ?_⟩
  · exact _root_.GlobalTheory.Mem.Top.Closing.memberE_closing_alt_alt hA.a1 hA.a2 hA.a3 hA.a11 hA.a10 hA.a6 hA.a12 hA.a13 hA.a14 hA.a16 hA.a17 hA.a18 hA.a8 hA.a6 hA.a7
      hA.a5 hA.a19 hA.a20 hA.a21 hL N Ng has3 lv lvg exp second toN
  · exact _root_.GlobalTheory.T.geometric_parameter_uniform_alt hH.h1.q12 hH.cover hA.a5 hA.a7 hA.a8 hA.a9 hA.a10 hA.a6 hA.a22 hA.a23 hA.a1 hL N (geoCl anyGeometry)
      (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)) rfl toB intersection_update_fsHerm_neg_one hMQ
theorem exists_baseLattice_of_prime_alt : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → ExistsUnlocalizedSaturatedState → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL → ∀ cDep : ℝ,
    _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)) → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s ∧
      GlobalTheory.Fc.ExBL KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s)
        (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry))) := by
  intro hA hE hH hW hL hN cDep hMQ
  have holdsW : WeightCaseCondition := _root_.GlobalTheory.T.w_of_weight_residue_char hH.h1 hH.h3 hH.multW
  have datE : DatExt := _root_.GlobalTheory.Mem.R3.Rw.datExt_of_hypotheses hH.cover hA.a5 hA.a6 hA.a7 hA.a8 hA.a9 hA.a10
  have h := _root_.GlobalTheory.T.all_stages_at_member_of_specializations_alt (by first | exact hA.a5 | exact hA.a7) (by first | exact hA.a5 | exact hA.a7)
  repeat (first | specialize h hA.a8 | specialize h hA.a9 | specialize h hA.a12 | specialize h hA.a5 | specialize h hA.a6 | specialize h hA.a7 | specialize h hA.a10 | specialize h hA.a22 | specialize h hH | specialize h hN.pr | specialize h hN.ser | specialize h hL | specialize h hN.arch | specialize h hN.pt)
  obtain ⟨sA, sMt, sRat, sCusp, -, -, -, sC, -, sl⟩ := h
  obtain ⟨fin, second⟩ := _root_.GlobalTheory.T.sFino_and_secondNo_of_sFinl' hH.cover (by first | exact hA.a5 | exact hA.a7) (by first | exact hA.a5 | exact hA.a7) hN.pr hN.ser datE holdsW hA.a9 hN.arch.pht hL sMt sRat sCusp cDep (sl cDep).2.2.2
  have has3 := _root_.GlobalTheory.Mem.Top.Bl.has3_neo_of_localLanglands_alt hL cDep hW sA sMt sRat sCusp (sl cDep).1 (sl cDep).2.1 (sl cDep).2.2.1 sC fin SExt.none (geoCl anyGeometry)
  have lv := _root_.GlobalTheory.T.lv3Mv_extensionWithOrigin_and_NEog hL cDep SExt.none (geoCl anyGeometry)
  exact _root_.GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_pair_alt hA hE hH hL hN (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨⟨h.1⟩, h.2.down⟩) has3 lv.1 lv.2 (_root_.GlobalTheory.T.slot_mv_extension_with_origin_geo_cl hL cDep anyGeometry)
    (second SExt.none (geoCl anyGeometry)) hMQ
end GlobalTheory.Mem.Top.Bl
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.member_exists_baseLattice_alt : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → ExistsUnlocalizedSaturatedState → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL → ∀ cDep : ℝ, _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)) → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s ∧ GlobalTheory.Fc.ExBL KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry))) := by
  first | exact @_root_.GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_prime_alt | exact _root_.GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_prime_alt | (intros; apply _root_.GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_prime_alt <;> assumption)
end
end
