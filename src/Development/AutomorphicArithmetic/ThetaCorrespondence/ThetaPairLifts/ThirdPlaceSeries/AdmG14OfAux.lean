import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralElementsFromIdempotentCoeffs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualFamiliesContinuous
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeCompletionDegreeOneCountProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalOfArtinReciprocity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCharactersTypePrimeProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMemAdjoin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpRangePositiveSignPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualJumpRangeNegativeSignPlaceProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftFMonoLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDirectLiftingProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDualLiftingProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeFamilyPotentiallyCrystallineCommonTameExtens
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousLoc
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SecondClosedOfFirstClosed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedGaloisRepCharacterBlocks
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeLocalGlobal
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeE
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosingAtRecord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodParIffGoodSig
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitLeOfFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatPowSubOneLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePeriodBoundAllConstantGeForty
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfLiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEuler
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalAbsorptionLengthBoundOfBlochKato
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualRepSpansMatrixAlgebraOfGoodPoint
import Formalism.SharpRestriction.LevelLetterCocycles.CongruenceAnnihilatesCharacterPart
import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionEveryLocalisation
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LemmaOpenOfIntegrality
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclusionOfAdmissiblesStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory.ClosingLocalInputs
theorem galoisFamilyConditions_of_sumRepresentations_alt (D : D7) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) : _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) :=
  fun i r hr => (h41 i).2.2 r hr
theorem main_alt_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris →
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ (C : ℝ) (CT : ℕ), 40 ≤ CT → 8 * (CT : ℝ) ≤ C → (∃ P : Pend D, admDZ P ∧ EigSpan P) →
    SumRepresentations.tie0 D → SumRepresentations.adm1 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → SumRepresentations.ConclusionG5 D → SumRepresentations.ConclusionG6 D →
    ResidualIrreducibleRankR D → GlobalTheory.TypeLeaf.SerLoc D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D → TieInePoly D → tieChi (D := D) →
    _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  intro hGAR hBS hFB hBKL hLTD hLEC D HW F Cm C CT hCT hC hP htie0 hadm1 hadm2 hadm5 h41 hG5 hG6 hN9 hSer hO
    hIne hChi
  obtain ⟨P, hDZ, hEig⟩ := hP
  have hT : admT (D := D) CT := _root_.GlobalTheory.InertiaEigenvalues.theoremT_all_records hBS hFB hBKL hLTD hLEC D HW F Cm CT hCT
  have hLOC : LocalPushoutProposition (D := D) := _root_.GlobalTheory.ClosingStatement.main hBKL hLTD hLEC D HW F Cm
  have hRbar : ResidualAbsIrreducible (D := D) := GlobalTheory.Pass.residualRep_spans_matrixAlgebra_of_goodPoint D hN9
  have hN5g : TypePrimeChoiceLemmas (D := D) := _root_.GlobalTheory.typePrimeCongruences_forall D ⟨hadm5, h41, hN9, hO⟩
  have hTB : admTB (D := D) HW F := _root_.GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar hBKL hLTD hLEC D HW F Cm
  have hBK : admBK (D := D) := _root_.GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ hBKL hLTD hLEC D
  exact _root_.GlobalTheory.T.admT_of_artin_reciprocity_and_local_conditions hGAR D P HW F C CT hC hadm5 hEig hIne hT hLOC hRbar hN5g hDZ
    (_root_.GlobalTheory.ClosingLocalInputs.galoisFamilyConditions_of_sumRepresentations_alt D h41) hG5 hG6 hSer hTB hBK hadm1 hadm2 htie0 hChi
end GlobalTheory.ClosingLocalInputs
end
