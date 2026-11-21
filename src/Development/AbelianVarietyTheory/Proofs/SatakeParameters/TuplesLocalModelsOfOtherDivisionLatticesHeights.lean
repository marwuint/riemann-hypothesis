import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteAdmissibleIndepDivisionLattices
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeChainComparisonIndepDivisionLattices

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

set_option maxHeartbeats 800000 in

theorem modelsAt_tr : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ),
    ModelsAt D O → ModelsAt (setDiv D N h) (O.tr N h) := by
  intro D O N h H hT hk
  obtain ⟨h0, LC, hLC⟩ := H hT hk
  refine ⟨h0, LC, fun μ hμ u w hg hq => ?_⟩
  obtain ⟨c1, c2⟩ := hLC μ hμ u w hg hq
  exact ⟨_root_.GlobalTheory.Svd.cmpLite_setDiv D N h _ _ u μ w hg _ _ _ c1, _root_.GlobalTheory.TwU.siteAdm_setDiv D N h u w hg _ _ _ c2⟩

end GlobalTheory.Svd
