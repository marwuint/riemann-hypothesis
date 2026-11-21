import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedLatticesTwoClassesAdmissible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryPeriodNeZeroAndLatticeLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumPairClassesExplicit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldKernelPushforwardEqHostKernelFunctionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPosBadPrimesNoConjugatePair

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem th_eq_kerTh : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', (t.rd u μ).Th t.seam t.amb i c c' = kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie Xi muT hL i hi c c'
  obtain ⟨hδ, -, hV, -⟩ := _root_.GlobalTheory.TieBase.base_data t
  obtain ⟨hl, hS⟩ := _root_.GlobalTheory.BadPrimes.lev_pos_and_noConj A dtU a hP hTie
  exact GlobalTheory.T.columnFieldKernel_pushforward_eq_hostKernelFunction t.seam t.seam_ok t.B t.χ _ (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')
    ((t.rd u μ).Xi i c c') t.cc_ok t.δ_ok hδ hV hl hS (_root_.GlobalTheory.TwV.adm_seam_lat_rd_pair t u μ i (i + 1) c c')
    (_root_.GlobalTheory.TwV.datLoc_classes A dtU a hP hTie Xi muT hL i hi c c')

end GlobalTheory.TwV
