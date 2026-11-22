import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Formalism.LocalToGlobal.FiniteTOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodTypesOfTypesTrue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqualMultiplicitiesRowTestOfSameGroupTransfer
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
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithAtProperty

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.LiteralAutomorphy
def witDropA_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} {A : AtP} {K : Ctx} {B : Base}
    {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {O : Obj2 (w.D Z)}
    (x : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s K w Z O) : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z O :=
  { x with nx := ⟨x.nx.1, x.nx.2.1⟩ }
theorem slot_mv_extension_with_at_property {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} (A : AtP)
    (hs : PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) : PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s := by
  intro K B f T w Z O x Nd h O' hO' col n
  obtain ⟨t, hobj, hrx, ⟨c⟩, hsx, hox⟩ := hs K B f T w Z O (_root_.GlobalTheory.Mem.LiteralAutomorphy.witDropA_alt x) Nd h O' hO' col n
  exact ⟨t, hobj, hrx, ⟨⟨c.1, c.2, x.nx.2.2⟩⟩, hsx, hox⟩
end GlobalTheory.Mem.LiteralAutomorphy
end
end
