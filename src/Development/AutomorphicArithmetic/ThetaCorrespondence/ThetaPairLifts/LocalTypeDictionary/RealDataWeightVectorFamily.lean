import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.Divisors.Params
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertJunkColIn3
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorsRowsLiftsRationalAdjointClosed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GUnitOfModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PGEquivOfBaseW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointLiftRangeLeGoodBlockEigenspaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialFixesVacuaGoodInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftScalarIdentityMatchingAdjointInjective
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransferEigensystemPartsThreeLevelsOfMultEq
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlacesOfCondition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodCharactersDualStableOfThetaLiftScalars
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTheoremAPublishedHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftSecondHypotheses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTestsModularLatticeOfCoreCompatibility
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeClose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWFormsEqPrincipalForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWOrthogonalSumOfParts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerProductEqConstMulLValue
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalSStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDoublingEqMatrixCoefficient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteStarCompMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoxProductsOrthogonalSumTargetCartanFock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralsVanishOfAllLiftsVanishStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesIntegralNonzeroConstant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaResidueNeZeroOfSimplePoleLiftLFunctionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKillingImpliesVanishing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelExistsForContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOfHeisDer
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWittDecompositionIsotropicSplitUnipotent
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilizeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaMajorantAverageIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVacuumVectorPrincipalCongruenceSupport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSumHyperbolicPlanesOrthogonalWittDecomposi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteRealGroupFixesSplitSpaceWeilVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteUnitaryQuotientCompactFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianSpaceDoubled
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionDoublingSeesawOfStandardChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingVectorFockPairIsCompactFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRightOfRapidDecayUnramifi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftNonvanishingOnStringOfDefiniteDown
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedThetaCorrespondenceAllGoodPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftEigenformIsEigenformStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationFinitePlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationAtRealPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypesExcludeLevelCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasStringOfLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeNZOfNonVanGen
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimplePoleOfHecke
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpInjWOfAForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftOntoOfInjectiveEigenspaces
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.SharpRestriction.ElevenLe
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateBaseLevelOfHoweUnramifiedCorrespondence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumSourceLevelCharacterLaw
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorMatrixCoefficientFormula
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteZetaIntegralThetaLiftEqPartialLValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaLiftInnerProductFormulaOfHyp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivEqZeroOfEven
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKTranslate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtLogCosh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixEntryNormSumUpperRightBlockElementPLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftScalarPosAllPlacesOfConjugateIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityOneGivesUnitEquiv
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LiftTestPositiveLevelsKappa
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PartialLFunctionOfPublished
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedScalarConjugationInvariance
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
namespace GlobalTheory.Stage4
theorem stage4_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).GalD F.cr false ∧ R.PPos := by
  intro P hHL D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O hT hG hM hRow hLv hPos
  have hE : GlobalTheory.Published.SiegelEisensteinContinuation := _root_.ResidueKilled.sec_of_dm P.q9
  obtain ⟨hOk, hGU, hGE, hBlk, hA, _hB⟩ := _root_.GlobalTheory.T.pgUnit_and_pgEquiv_of_multEq P R F hT hM
  obtain ⟨hLT, hLTB, _hML⟩ := _root_.GlobalTheory.PrimIn.liftTests_and_mLat_of_ties T R F κ v₀ O hT hG
  obtain ⟨hLevW, hPartsW, hHecke, hSep, _hTr⟩ := _root_.GlobalTheory.T.pLevW_and_trISep_of_liftTest_pos P R F hT hM hG.unif hLT hLv hPos
  have hOnto := _root_.GlobalTheory.T.partial_L_function_of_hypotheses_alt P.q5 P.q4 P.q2 P.q1 P.q7 P.q9 P.q10 P.q11 hHL (s := 1) R F hT.ok hT.char hT.ex hT.host
    hT.params hT.ccK hT.guard hT.types hOk.2 hGE hG.unif
  obtain ⟨fw, hBar⟩ := hG.fw
  have hGal : (R.toCx3 F).GalD F.cr false :=
    _root_.GlobalTheory.T.twisted_scalar_conjugation_invariance hE P.q1 P.q2 P.q13 P.q11 P.q9 P.q14 P.q10 P.q7 P.q4 T R F κ v₀ O 1 hT.ok hSep hT.char hT.ex hT.params
      hT.phs hT.std fw hBar hG.ioExt hG.pins (fun i => (hG.oneMap i).1) hG.phase hOk.1 hOk.2 hHecke hGU hGE hBlk hRow hLT hLTB
      hOnto hPos.1 hPos.2 hG.unif hLevW hA hPartsW
  exact ⟨hGal, _root_.GlobalTheory.PosScalRed.posScal_of_galD R F hT.ok hT.char hT.ex hPos hGal hG.unif hLTB hGE⟩
end GlobalTheory.Stage4
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_data_weight_vector_family_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).GalD F.cr false ∧ R.PPos := by
  first | exact @_root_.GlobalTheory.Stage4.stage4_alt | exact _root_.GlobalTheory.Stage4.stage4_alt | (intros; apply _root_.GlobalTheory.Stage4.stage4_alt <;> assumption)
end
