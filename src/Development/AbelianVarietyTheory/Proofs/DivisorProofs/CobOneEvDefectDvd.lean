import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffsInIdealOfPowerSeriesIffImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoboundaryRepresentativeCocycleRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquarePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvSubstNatMultiplePrimePowConstant
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem cobOne_ev_defect_dvd : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect c.μ (p ^ n) f → ∃ z, cobOne O (G.A n) (c.ev n s) = (p : O) ^ n • z := by
  intro p _ O E _ _ _ hF G d c f hf n s hs
  haveI : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete
  obtain ⟨hf0, -, hfc⟩ := hf
  obtain ⟨κ, -, hκ⟩ := ((series_in_ideal_iff_image O E (Fin d ⊕ Fin d) ⊤ _).1).1 hfc
  obtain ⟨-, hκ0, hrest⟩ := _root_.GlobalTheory.QLog.integral_cob_defect_rules O E d c.μ c.isLaw hF.inj f κ hκ
  have hcob := (hrest (p ^ n) s hs).1
  refine ⟨c.ev₂ n κ, ?_⟩
  rw [← (GlobalTheory.T.formalChart_evalSquare_properties p O G d c n s).2.2.2, hcob, map_sub, map_smul,
    (_root_.GlobalTheory.QLog.Chart.ev_nmul_pow p O G d c n).2.1 κ, hκ0 hf0, map_zero, sub_zero, Nat.cast_pow]

end GlobalTheory.QLog
