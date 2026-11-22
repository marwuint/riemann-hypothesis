import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassC0PrimeNotExceptional
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LamPosGOfLamPos
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitDetFrameMatrixOfCharts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalLocalBasesCarryWittLattices
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFiniteDataLevelPosBadPrimeFactors
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteResidueCharNotMemBadPrimes
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteBaseDatumIntegralOffBadPrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem kernelSite_seriesData_below_lastStep : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Pair → S.Pos → S.Scal → S.K1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hD hP hPos hSc
  refine ⟨?_, ?_, ?_, hSc, J.rho std, ?_, ?_, ?_⟩
  · intro j hj L0 hL0 La' hLa'
    exact (hP j hj L0 La' (repOf_lat _ _ j L0 hL0) hLa').1
  · obtain ⟨hpos, hS⟩ := _root_.GlobalTheory.TwV.sNum_lev_site t std J
    exact ⟨hpos, fun hd => _root_.GlobalTheory.TwV.SitePrime.resChar_not_mem_S t std J (hS _ Fact.out hd)⟩
  · exact ⟨(t.O u μ).S, _root_.GlobalTheory.TwV.SitePrime.resChar_not_mem_S t std J, fun j _ L0 _ La' _ y => _root_.GlobalTheory.TwV.Joint.site_base_datum_integral_off_bad_primes t std J S j L0 La' y⟩
  · exact GlobalTheory.TwU.lamPosG_of_lamPos _ S.E D _ _ _ hPos
  · exact fun j La v => GlobalTheory.isUnit_det_frameMatrix_ofCharts _ _ _ j La v
  · refine _root_.GlobalTheory.TwV.frameLatMapLt_of_ties _ S.hfin D (J.fd std) (J.rho std) (halfDiffInv_integral_at_split D _ _ hg) ?_
    intro j hj La La' h1 h2
    have q := hP j hj La La' h1 h2
    exact ⟨q.1, fun v => ⟨(q.2.2.2.2.2.2.2 v).2.2.1, (q.2.2.2.2.2.2.2 v).2.2.2⟩⟩

end GlobalTheory.TwV

end
