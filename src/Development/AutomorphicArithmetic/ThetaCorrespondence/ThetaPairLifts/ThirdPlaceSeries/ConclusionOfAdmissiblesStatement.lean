import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
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
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclusionOfAdmissibles

set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admT_of_artin_reciprocity_and_local_conditions : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C → SumRepresentations.adm5 D → EigSpan P → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) → admG5 (D := D) → admG6 (D := D) → GlobalTheory.TypeLeaf.SerLoc D → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  exact @_root_.GlobalTheory.admT_of_adm5_eigSpan_tieInePoly
end
