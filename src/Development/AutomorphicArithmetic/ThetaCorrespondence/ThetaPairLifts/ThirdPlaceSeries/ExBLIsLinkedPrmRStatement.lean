import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
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
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExBLIsLinkedPrmR

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_parameter_uniform_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → PositionMv p.s → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat) → GlobalTheory.Fc.ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) := by
  first | exact @_root_.GlobalTheory.Mem.Top.Bl.exBL_isLinked_prmR_alt | exact _root_.GlobalTheory.Mem.Top.Bl.exBL_isLinked_prmR_alt | (intros; apply _root_.GlobalTheory.Mem.Top.Bl.exBL_isLinked_prmR_alt <;> assumption)
end
