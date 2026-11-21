import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFormalGroupLawCoboundaryOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalChartQuotientByIdealWithPrimePow
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem coeff_mem_ideal_of_formalGroupCoboundaryOne_coeff_mem : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ I : Ideal O, (p : O) ∈ I → ∀ s : MvPowerSeries (Fin d) O, (∀ α, coeff α (cob1 c.μ s) ∈ I) → ∀ α, coeff α s ∈ I := by
  intro p _ O _ G d c I hp s hs α
  obtain ⟨c', hlaw, -, -⟩ := _root_.GlobalTheory.QLog.ChartRed.exists_chart p O G d c I 1 (by rwa [pow_one])
  have hpk : ((p : ℕ) : O ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]; exact hp
  have hmap := (_root_.GlobalTheory.Katz.map_cob_swap_pull O d c.μ c.isLaw.const (O ⧸ I) (Ideal.Quotient.mk I)).1 s
  have hz : map (Ideal.Quotient.mk I) (cob1 c.μ s) = 0 := by
    ext β
    rw [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hs β
  rw [hz] at hmap
  have h0 := GlobalTheory.Katz.eq_zero_of_cob1_eq_zero p (O ⧸ I) hpk d (G.baseChange (O ⧸ I)) c'
    (fun i => map (Ideal.Quotient.mk I) (c.μ i)) hlaw (map (Ideal.Quotient.mk I) s) hmap.symm
  have := congrArg (coeff α) h0
  rwa [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at this

end GlobalTheory.QLog
