import Formalism.FilteredPoleLength.ReducedBasisBounds.ReductionQuotient

namespace Formalism.LatticeBaseChangeAlt

theorem poleOrderGood : PoleOrderGood := by
  intro ep T ν νs c' vet e hep hc hv hν ⟨n, hn⟩ he
  have hepR : (1 : ℝ) ≤ ep := by exact_mod_cast hep
  have hT0 : (0 : ℝ) ≤ T := by positivity
  have hy : 0 ≤ (ep : ℝ) * (T * c' * vet) := by positivity
  rw [div_le_iff₀ (by linarith)]
  have hint : (ep : ℝ) * ((T : ℝ) * ν - e) = (((T : ℤ) * n - ep * e : ℤ) : ℝ) := by
    push_cast; rw [← hn]; ring
  rw [hint, Int.ceil_intCast, Int.cast_max]
  apply max_le
  · simpa [mul_comm] using hy
  · rw [← hint]
    have : (T : ℝ) * ν - e ≤ T * c' * vet := by nlinarith
    nlinarith

theorem poleOrderBad : PoleOrderBad := by
  intro ep T ν νs c' vet hep hT hc hv hν e
  have hepR : (1 : ℝ) ≤ ep := by exact_mod_cast hep
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have he : (T : ℝ) * (νs + 1) ≤ (e : ℝ) := Int.le_ceil _
  have hy : 0 ≤ (ep : ℝ) * (T * c' * vet) := by positivity
  rw [div_le_iff₀ (by linarith)]
  have hx : (ep : ℝ) * ((T : ℝ) * ν - e) ≤ (ep : ℝ) * (T * c' * vet) - ep := by
    have : (T : ℝ) * ν - e ≤ T * c' * vet - 1 := by nlinarith
    nlinarith
  have hc1 : ((⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) < (ep : ℝ) * ((T : ℝ) * ν - e) + 1 :=
    Int.ceil_lt_add_one _
  rw [Int.cast_max]
  apply max_le
  · simpa [mul_comm] using hy
  · nlinarith

end Formalism.LatticeBaseChangeAlt
