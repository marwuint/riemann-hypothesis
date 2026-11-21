import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralRationalAtMember
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActionReadAtMember
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFinEMemDivisorStandard
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateBlockUpperOfEigenfunctionUnipotentType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralFrameSplitNontrivialAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueNeZeroOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.G0LiftUnitaryCentralFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjParahoricBlockLift
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CenRatAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ActReadAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameAtOfLayerStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.CenLocAt
theorem exists_ad_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ c => Nonempty (MtAd t.r.Y c.a.all.gal.mt) :=
  GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE _ _ => hE.elim fun e => ⟨_root_.GlobalTheory.HeightCounting.RealExpansionExtraData.ad e⟩
set_option maxHeartbeats 2000000 in
theorem cenLoc_at_member : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ c => CenLoc (w.D Z) c.a.all.gal.mt := fun hL =>
  _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.cenRat_at_members hL) (_root_.GlobalTheory.T.actRead_at_member_of_recT hL)) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.frameAt_of_tup_eq_mu_at_members hL) (_root_.GlobalTheory.CenLocAt.exists_ad_alt hL)))
    fun _ _ _ _ _ _ _ _ t _ _ _ h => h.2.2.elim fun ad => cenLoc_of t.r.Y t.r.z.cG _ ad h.1.1 h.1.2 (h.2.1 ad)
end GlobalTheory.CenLocAt
end
