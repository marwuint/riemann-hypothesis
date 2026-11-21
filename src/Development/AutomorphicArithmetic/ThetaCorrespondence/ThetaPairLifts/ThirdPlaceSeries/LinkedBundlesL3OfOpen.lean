import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisorAll
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyHypothesesOfWorkingClassSevenDuties
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoices
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvInjOfIsModelsOfTie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JEvExistsAndJEvBar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeoAct
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.RealPins
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFramesNormalAtLevelPlacesOfCharFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIoExtensionOfWeakCharacterisationFrames
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEveryEmbeddingThirdKind
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Formalism.LocalToGlobal.IndefiniteReal.RealRec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftRowFiresOfWeakCharacterisation
import Formalism.LocalRingCardinality.NFLeTwoMulTSq
import Formalism.LocalRingCardinality.DataNChTie
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionFirst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionThird
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideCardEqOfCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowOfCovolumeOntoGrid
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedTiesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWPRowsOfRows
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupAllUsedPart
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventualL3OfCovolume
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Glob.CovolRow
theorem linked_bundles_l3_of_open_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.NT.RayField → _root_.GlobalTheory.CovTop.CovolumeBoundOfX → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.S0.CovolumeBoundThirdPlaceSeries := by
  intro hDS hHC hCR hCW hRay hCov hL N S Γ hN o
  have hA := _root_.GlobalTheory.T.class_sum_divisor_all_alt hRay hL N S Γ hN o.hDivG
  obtain ⟨R, hR, h⟩ := RowL.and (RowL.and (RowL.and (RowL.and o.hPA o.hDivG) o.good) o.geo) hA
  refine ⟨R, hR, h.imp fun 𝒜 σ hsel H => ?_⟩
  obtain ⟨⟨⟨⟨hpa, hdv⟩, hgd⟩, hgeo⟩, hall⟩ := H
  choose τ hτ using fun {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) x hx i => hgeo Fm hc x hx i
  let τ' : _root_.GlobalTheory.Fc.CompatibleSelection σ := fun Fm hc x hx i => τ Fm hc x hx i
  have hduty : ∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm := fun _ Fm hc =>
    let ⟨_, _, h7, _⟩ := hsel Fm hc
    (DQ.familyClass_sevenDuties_and_stableLattices _ Fm h7).1
  have hrows : Ind.EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := _root_.GlobalTheory.Fc.Ind.evW_pRows_of_rows_alt hDS hHC hCR hCW 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') (fun Fm hc x hx i => hpa Fm hc x hx i)
    (fun Fm hc x hx i => _root_.GlobalTheory.Fc.FourBoundsAtBundles.p_div_of_div3g _ (hdv Fm hc x hx i)) hgd
    (fun Fm hc x hx i => ⟨(hτ Fm hc x hx i).2.1, (hτ Fm hc x hx i).2.2.1⟩)
  exact _root_.GlobalTheory.Fc.Ind.eventual_L3_of_covolume_alt hCov 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') hduty hrows
    (GlobalTheory.Fc.FourBoundsAtBundles.evW_of_atAll fun Fm hc x hx i => (hall Fm hc x hx i (τ Fm hc x hx i)).2.2.2.1)
end GlobalTheory.Glob.CovolRow
end
