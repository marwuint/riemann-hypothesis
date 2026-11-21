import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomRhoK
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusLiftMovesLetterCoordinates
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalLocalBasisCoordinatesDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaTauOrthonormalBasisSumCoordinates
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLocalBasisStandardCoordLeOneInert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesIntegralSigmaSqFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesIsotropic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceDualExpansionOrbitLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearFormsHyperbolicCoordinatesEqTarget
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesScaledEqOrthonormalBasisSeries

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

open GlobalTheory.KerStd.HypCoord in

theorem GlobalTheory.KerStd.hyp_of_stdBases : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∀ (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p), OwOK (nP D p) σ om oms → TrDual (nP D p) σ om oms → ∀ (R : Finset (OrbitPlaces.Pl D)), OrbitPlaces.IsReps D p R → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → TaylorLogMetric.Orthonormal D b → ∃ f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p, HypPair σ f f' ∧ ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (hypZ D p σ om oms R f f') (thOrth D lam c b G) := by
  intro D p _ lam σ hσ hO hcl om oms hOw hTr R hR N N' L L' P P' hA hP hP' r b hb ho
  have hcl' : IsResidueClassZero D p ∨ IsSg D p := hcl.elim (fun h => Or.inl h.1) Or.inr
  have hONB : Formalism.L2.KerInert.RepFrame.LamONB D lam b :=
    Formalism.L2.KerInert.RepFrame.lamONB_of_cols D lam b
      (Formalism.L2.KerInert.RepFrame.rank_of_locBasis L L' hA.2.2.1 hA.2.2.2 b hb)
      (Formalism.L2.KerInert.RepFrame.cols_of_trace D (Formalism.L2.KerInert.RepFrame.trace_tau_sum D) lam b ho)
  obtain ⟨hg, hh⟩ := _root_.GlobalTheory.KerStd.HypCoord.FrobMove.frob_moves_coords D p lam σ hσ hcl' N N' L L' P P' hP hP' r b
  have hpair := _root_.GlobalTheory.KerStd.HypCoord.hK_gK_dual D p lam σ hσ hcl' N N' L L' P P' hP hP' r b hONB
  have hiso := norm_sigma_eq p σ hσ
  have hhint := _root_.GlobalTheory.KerStd.HypCoord.norm_hK_le_one D p lam σ hσ hcl' N N' L L' P P' hP hP' r b hb
  have hgint : ∀ z a b₀ i, ‖gK D lam P P' b z a b₀ i‖ ≤ 1 := fun z a b₀ i => by
    rw [← hiso, hg]; exact hhint _ _ _ _
  have hg2 : ∀ z a b₀ i, σ (σ (gK D lam P P' b z a b₀ i)) = gK D lam P P' b (posPl D p z 2) a b₀ i :=
    fun z a b₀ i => by rw [hg, hh, posPl_add]
  obtain ⟨hf1, hf2⟩ := _root_.GlobalTheory.KerStd.HypCoord.fOf_integral_sigma_sq D p σ om oms R N N' r (gK D lam P P' b) hO
    (fun x hx => by rw [hiso]; exact hx) hOw hgint hg2
  obtain ⟨hi1, hi2⟩ := _root_.GlobalTheory.KerStd.HypCoord.fOf_isotropic D p σ om oms R N N' r (gK D lam P P' b) (hK D lam P P' b) hO hR hg hpair
  have hd := _root_.GlobalTheory.KerStd.HypCoord.fOf_fOf'_dual D p σ om oms R N N' r (gK D lam P P' b) (hK D lam P P' b) hO hR hTr hg hpair
  refine ⟨fOf D p σ om R (gK D lam P P' b), fOf' D p σ oms R (gK D lam P P' b), ⟨hf1, hf2, hi1, hi2, hd⟩, ?_⟩
  have hlin := _root_.GlobalTheory.KerStd.HypCoord.linForm_hypZ D p σ om oms R N N' r _ (gK D lam P P' b) (Formalism.L2.KerInert.RepFrame.lamB D lam b)
    (fun k j => chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) hO hR (_root_.GlobalTheory.KerStd.HypCoord.trDual_expand D p σ om oms hTr)
    (fun q z a b₀ => _root_.GlobalTheory.KerStd.HypCoord.lamB_sum_gK D p lam σ hσ hcl' N N' L L' P P' hP hP' r b hONB q z a b₀)
  refine _root_.GlobalTheory.KerStd.HypCoord.stdSer_scaled_eq_thOrth D p lam N N' r P P' b _ (fun i => ?_) hlin
  simp only [hypZ, linEv, linOd, map_sum, map_add, map_mul, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_X,
    mul_zero, apply_ite MvPowerSeries.constantCoeff, map_zero, ite_self, Finset.sum_const_zero, add_zero]
