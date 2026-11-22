import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCoverOverSizedField

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.DeepExist

theorem floorThreeLOverLogThree_mul_log_fifteen_le {L : ℝ} (hL : 0 ≤ L) : (expL L : ℝ) * Real.log 15 ≤ 9 * L := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have he : (expL L : ℝ) ≤ 3 * L / Real.log 3 := Nat.floor_le (by positivity)
  have he' : (expL L : ℝ) * Real.log 3 ≤ 3 * L := (le_div_iff₀ h3).1 he
  have h15 : Real.log 15 ≤ 3 * Real.log 3 := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 15) (by norm_num : (15 : ℝ) ≤ 3 ^ 3)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have he0 : (0 : ℝ) ≤ expL L := Nat.cast_nonneg _
  nlinarith

theorem size_le {D : D7} {L : SizeData₂ D} {PP A M o : ℝ} (hN : HostNum D L PP A M) (hF : o ≤ 217 * zBase L ^ 2) :
    o + 20 * (Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ expL L.sc.L) + Real.log D.host.d + 1) ≤
      391 * zBase L ^ 2 := by
  have hL10 := hN.big.2.1
  have hcop := hN.cop
  have h01 : D.host.g 0 * D.host.g 1 ≠ 0 := fun h => by
    rw [h, Nat.coprime_zero_right] at hcop
    norm_num at hcop
  have hg0 : ((D.host.g 0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (mul_ne_zero_iff.1 h01).1
  have hg1 : ((D.host.g 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (mul_ne_zero_iff.1 h01).2
  have h15 : ((15 : ℝ) ^ expL L.sc.L) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hlog : Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ expL L.sc.L) =
      Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) + expL L.sc.L * Real.log 15 := by
    rw [Real.log_mul (mul_ne_zero hg0 hg1) h15, Real.log_mul hg0 hg1, Real.log_pow]
  have he := floorThreeLOverLogThree_mul_log_fifteen_le (L := L.sc.L) (by linarith)
  have a0 := hN.logg 0
  have a1 := hN.logg 1
  have ad := hN.logd
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hZ : 8 * L.sc.L ≤ zBase L := by
    unfold zBase
    have : (8 : ℝ) ≤ D.R.f * D.R.r := by nlinarith
    nlinarith
  rw [hlog]
  nlinarith

end GlobalTheory.CovTop.DeepExist

end
