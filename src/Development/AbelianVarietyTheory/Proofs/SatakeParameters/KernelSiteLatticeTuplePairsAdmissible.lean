import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerThEntireAlgCoef
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiDetIdAndChiFacAlg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitDetFrameMatrixOfCharts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedPairDatumDependsOnlyOnLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeSelfDualEvenRankAtSite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTuplePairScalarMemAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFiniteDataLevelPosBadPrimeFactors
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameLocalLatticeSpanKernelLatticeZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameLocalLatticeSpanKernelLatticeSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteBaseDatumIntegralOffBadPrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
open Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem pairOK_allSites : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  intro j hj La La' hL hL'
  have hm : (sysS H X std).mm = D.R.m := by
    first | (rfl; done) | exact X.fl_m | exact I.fl_m
  have hjm : j + 1 ≤ D.R.m := hm ▸ hj
  have hSD0 := _root_.GlobalTheory.KerSiteSelfDual.even_and_isSDLat_kerN t std J hD j (by omega) La hL
  have hSD1 := _root_.GlobalTheory.KerSiteSelfDual.even_and_isSDLat_kerN t std J hD (j + 1) hjm La' hL'
  have hA : TaylorLogMetric.admitted D _ _ ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') := ⟨hSD0.1, hSD1.1, hSD0.2, hSD1.2⟩
  have hInt : ∀ x, IntOff (t.O u μ).S (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' x) :=
    fun x => _root_.GlobalTheory.TwV.Joint.site_base_datum_integral_off_bad_primes t std J S j La La' _
  have hK := GlobalTheory.kerTh_entire_algCoef D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (ssRec t u μ) (t.rd u μ).lev _ _ _
    (t.O u μ).S hA (_root_.GlobalTheory.TwV.sNum_lev_site t std J) hInt
  have hC := (GlobalTheory.SelfDualChiAlg.chi_detId_and_chiFac_alg D t.χ t.χ_ok).2 _ _ hA
  have hsp : ∀ (i : ℕ) (hi : i ≤ D.R.m) (Lb : (sysS H X std).Lt i), ((sysS H X std).Pj i).IsLatTup Lb.2 → ∀ v,
      locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN i Lb) =
        ((sysS H X std).latAt v i Lb.2).map ((((J.fd std).frM i Lb v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
    intro i hi Lb hLb v
    cases i with
    | zero => exact _root_.GlobalTheory.TwV.Joint.locSp_kerN_zero t std J hD Lb hLb v
    | succ k => exact _root_.GlobalTheory.TwV.Joint.locSp_kerN_succ t std J hD k hi Lb hLb v
  refine ⟨hA, _root_.GlobalTheory.TwU.xiM_datLoc t std J S hD j hj La La' hL hL', hK.1, hK.2, _root_.GlobalTheory.TwV.latticeTuplePairScalar_mem_algebraicClosure_alt t std J S hD j hj La La' hL hL',
    hC.1, hC.2, fun v => ⟨?_, ?_, hsp j (by omega) La hL v, hsp (j + 1) hjm La' hL' v⟩⟩
  · exact GlobalTheory.isUnit_det_frameMatrix_ofCharts (J.cp std) J.a ∅ j La v
  · exact GlobalTheory.isUnit_det_frameMatrix_ofCharts (J.cp std) J.a ∅ (j + 1) La' v

end GlobalTheory
