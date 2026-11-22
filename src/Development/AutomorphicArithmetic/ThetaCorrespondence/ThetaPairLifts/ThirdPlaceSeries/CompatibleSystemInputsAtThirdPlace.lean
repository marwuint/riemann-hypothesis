import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GaloisRepDescendsAtRealPlaces
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FittingLaterStagesRowIsConstructionState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizeParametersNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTypesOfTypesTrueReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GapRAllSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigenReadThirdLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AgreeOfData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.E0ReadOfEigenLabeling
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOfLocalLanglands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesLocalOfHypothesis
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
import Formalism.LocalToGlobal.FiniteTOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankIsotEqIsotL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoeffInvEqCoeff
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleRationalClassKernelIntegrals
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRegularSemisimpleOfTestFunctionNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHasSumEqIntegralIndicatorHasSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumConjClassesRegroupWithInvariantSelection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceInputsImplyCuspidalTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalSpectrumFinitenessOfDecayHarishChandra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricExpansionOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicTermsVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleTorusEllipticElementRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerTorusEllipticElementRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRealPlaceTorusClassesSignVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDiscreteSeriesCharacterEqWeylCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSeparationOfIwahoriTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableOrbitalIntegralPreservedLatticeIsometryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudocoefficientTraceVanishes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLowKOfLeLowKSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedIntertwiningIntegralNonzero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CapelliOfGelfand
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlRelationsOnKFiniteVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalInvariantSubspace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HyperbolicPairSplitTorus
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefExtendsHolomorphically
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWordTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsometryIntertwinesEnveloping
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerNonzeroOnGeneratingSet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthFilterFinRange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvalues
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicAndConstantTerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalOperatorsVanishingRadicalIntegralsUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EllipticPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalTraceMultiplicityGiven
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InfinitesimalCharacterReference
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsPositiveScalarsWithoutCongruenceLengthsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefficientFieldRingOfIntegersThird
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UpperRamificationJointConditionThirdJump
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UpperRamificationThirdJumpHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemPartitionLambda
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThirdSeriesWithLocalConditions
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOLaws

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PtInputsX
theorem inputs_at_third_place_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility →
    AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x,
    _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → Nonempty (_root_.GlobalTheory.NRows.LinkedInputs hL D') := by
  intro hL hP hX
  have h := (((_root_.GlobalTheory.T.compatible_system_third_place_linked_data hL hP hX).and (_root_.GlobalTheory.HeightCounting.Up.JointConditionThird.upper_ramification_joint_condition_third_jump_alt hL hP)).and
    (_root_.GlobalTheory.T.third_member_upper_ramification' hL hP)).and ((_root_.GlobalTheory.T.adm8_and_lamUsed_of_geometric_galois_compat hP hX).and (_root_.GlobalTheory.T.ser_loc_eventually_of_built hL hP))
  refine h.trans (StepW.of_all fun K B f T w _ _ hh P x l => ?_)
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h45, h6⟩ := hh
  have h4 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalTheory.NRows.LamUsed D' :=
    ⟨fun _ => ∅, fun _ _ _ => (h45 P x).2⟩
  have h5 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → SumRepresentations.adm8 D' :=
    ⟨fun _ => ∅, fun _ _ _ => (h45 P x).1⟩
  have e := fun (P₁ P₂ : D7 → Prop) => _root_.GlobalTheory.CoefDuty.LargeRing.evO_laws_alt _ _ _ l.a.A l.mt.M l.c.ch l.c.tp.tup P₁ P₂
  have a := (e _ _).1 (h1 P x l) ((e _ _).1 (h2 P x l) ((e _ _).1 (h3 P x l) ((e _ _).1 h4
    ((e _ _).1 h5 (h6 P x l)))))
  refine (e _ _).2.1 (fun D' hD' hO => ?_) a
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hD'
  obtain ⟨T⟩ := t1 hO
  exact ⟨⟨T, ⟨hO, t2 hO, t3 hO, t4 hO, t5 hO, t6 hO,
    _root_.GlobalTheory.T.galoisRep_descends_at_real_places hP.decay hP.howe hX D' T.P.cf T.P.C T.P.tp T.X⟩⟩⟩
end GlobalTheory.PtInputsX
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_nonempty_inputs_of_level_c : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → Nonempty (_root_.GlobalTheory.NRows.LinkedInputs hL D') := by
  first | exact @_root_.GlobalTheory.PtInputsX.inputs_at_third_place_alt | exact _root_.GlobalTheory.PtInputsX.inputs_at_third_place_alt | (intros; apply _root_.GlobalTheory.PtInputsX.inputs_at_third_place_alt <;> assumption)
end
end
