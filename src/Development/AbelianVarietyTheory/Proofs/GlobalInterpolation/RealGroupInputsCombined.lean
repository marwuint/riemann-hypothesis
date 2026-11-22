import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypesViaFullHeckeAlgebraEigensystemsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankIsotEqIsotL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoeffInvEqCoeff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodTypesOfTypesTrue
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.RL.LamLinked

theorem evP_params : EvP fun _ K => ∀ β : BPt K, Nonempty (ParameterChoice' β.D β.O.L) := by
  refine EvP.of_ev ⟨1, one_pos, fun eps C8 he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, hN⟩ := hN ch hch
  refine ⟨x0, fun K h1 h2 h3 h4 hx β => ?_⟩
  have hsc : β.O.L.sc = K.s := β.sc
  have hv : Val C cD ch β.O.L := by
    rw [← h1, ← h2, ← h3]
    exact β.p.pt_val β.val
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ (by rw [hsc, h4]) (by rw [hsc]; exact hx) hv (GlobalTheory.Plug.hostArith_bpt β)
  exact ⟨N.params⟩

end GlobalTheory.Fc.RL.LamLinked

namespace GlobalTheory.Fc.RL

end GlobalTheory.Fc.RL
