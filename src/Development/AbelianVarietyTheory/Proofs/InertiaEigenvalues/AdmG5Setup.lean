import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Formalism.SharpRestriction.LevelLetterCocycles.RestPt
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondTBAtRange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AmbientH1fOfLocalFiniteness
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientExtensionDecomposition
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientTypeConjugatePlaceAtSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionAtGoodPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAssembly
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualAbsIrredGoodPointOfResidualIrred
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.SemisimpleDecompositionOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeExceedsConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignsAndJumpSetsAtTypePrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointConditionsOfPointGaloisRepFamilies
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalCompatibilityAtTypes
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LNotMemGset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmFonOfPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockAndTorsionExponentBoundsCanonicalHubData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAbove
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAway
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentLeOfJumpsAtEmbeddingsUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostCompletionLeMaxUnramifiedPadic
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankLeOfSubsetClosureRange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiCrysOfConstituent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitRowPrimeOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleAtGoodPointsOfCoefRingTakenAtLiveStatement
import Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientFiltrationEveryDeclarationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientDualCrystallineAndPureOfDecompStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2OfDecomposition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientJumpBlockOfAdmissibleDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOneAwayFromType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLocalCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiAtPsiAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoFiniteTrivialRepUnramifiedColumnPlacesAStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Formalism.AdmissibleDesigns.AdmG5OfAdm51AdmG5
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLinkTameShape

theorem splitL_diagonal {K : Type} [Field K] (a b n : ℕ) (hn : n = a + b) (c : K) (y : Fin n → K) :
    Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL a b n hn ((Matrix.diagonal fun k : Fin n => if (k : ℕ) < a then 1 else c).mulVec y) =
      ((Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL a b n hn y).1, c • (Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL a b n hn y).2) := by
  ext j
  · simp [Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL, Matrix.mulVec_diagonal]
  · simp [Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL, Matrix.mulVec_diagonal]

theorem rhoBarTw_eq (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (a : ℤ) : rhoBarTw D.nd ρ π a =
      twistRep (glRep (redRep D.nd i (ρ π))) (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i a) := by
  have hz : ∀ (u : (D.nd.O i)ˣ) (n : ℤ), IsLocalRing.residue (D.nd.O i) ((u ^ n : (D.nd.O i)ˣ) : D.nd.O i) =
      (IsLocalRing.residue (D.nd.O i) u) ^ n := by
    intro u n
    have := congrArg Units.val (map_zpow (Units.map (IsLocalRing.residue (D.nd.O i)).toMonoidHom) u n)
    rw [Units.val_zpow_eq_zpow_val] at this
    simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] using this
  have hs : ∀ (c : D.nd.O i) (M : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)),
      (c • M).map (IsLocalRing.residue (D.nd.O i)) =
        IsLocalRing.residue (D.nd.O i) c • M.map (IsLocalRing.residue (D.nd.O i)) := fun c M => by
    ext; simp
  refine MonoidHom.ext fun g => LinearMap.ext fun u => funext fun k => ?_
  simp [rhoBarTw, twistRep, glRep, matRep, mapM, twistM, redRep, mapRep, Formalism.MainNotions.SumRepresentations.At.chiEpsBar, rhoO]
  rw [hs, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, hz, map_units_inv]

end GlobalTheory.NLinkTameShape

end
