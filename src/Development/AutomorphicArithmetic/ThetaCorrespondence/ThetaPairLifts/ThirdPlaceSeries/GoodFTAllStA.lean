import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClassMapCorrespondence
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeComponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentStarCompatibleOfLabellingAgree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameParameterCoupled
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateVectorInSubspace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabFixedOfTypesTrue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InfinitesimalCharacterReference
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzBigDef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodFTAllOfLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsRc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameParamRecordLe
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace DiscreteGroups.sglob.DzType.Rt
set_option maxHeartbeats 2000000 in
theorem goodFTAll_stA_alt (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt)
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf rep) (hlab : GlobalTheory.CoefDuty.OPinModel.LabFixed D)
    (hloc : ∀ (I : GlobalTheory.TypeRec.Ident D) cp, GlobalTheory.TypeRec.IsComp I rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (x : V),
      (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧
        (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom D.ntypes.e0 x = x) : GoodFTAll D := by
  refine _root_.DiscreteGroups.sglob.DzType.Rt.goodFTAll_of_local_alt hG hZ hL D a.A.wdT a.A.row rep
    (fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) a.row a.depth hlab
    (fun k => @GlobalTheory.DepthZeroCusp.depthZeroCuspidal (D.host.g k) ⟨D.host.g_prime k⟩) ?_ hloc
  intro I rc hrc k v
  refine _root_.DiscreteGroups.sglob.DzType.Rt.tame_param_le_of_tame_coupled hDZ hL D a.A.wdT I rc hrc (fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) k v (a.A.grp.kv k v) ?_
  rw [← a.zeta k]
  exact a.A.grp.tg_tame k v
end DiscreteGroups.sglob.DzType.Rt
end
