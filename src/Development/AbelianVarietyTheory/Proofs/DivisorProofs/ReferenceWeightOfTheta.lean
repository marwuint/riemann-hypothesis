import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfMemBadPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthUnitSizeBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceExponentPrimeBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientWeightGapBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.ToWeight

theorem sum_padicValNat_log_le (N : ℕ) (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∑ q ∈ S, (padicValNat q N : ℝ) * Real.log q ≤ Real.log N := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ q ∈ S, (padicValNat q N : ℝ) * Real.log q = ∑ q ∈ S, (N.factorization q : ℝ) * Real.log q :=
        Finset.sum_congr rfl fun q hq => by rw [Nat.factorization_def N (hS q hq)]
    _ ≤ ∑ q ∈ S ∪ N.factorization.support, (N.factorization q : ℝ) * Real.log q :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun q _ _ =>
          mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    _ = _ := (Finset.sum_subset Finset.subset_union_right fun q _ hq => by
          rw [Finsupp.notMem_support_iff.1 hq]; simp).symm

theorem sum_different_le (E : Type) [Field E] [NumberField E] (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∑ q ∈ S, (different_vp E q : ℝ) * Real.log q ≤ lrd E := by
  have hn : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have h := sum_padicValNat_log_le (discr E).natAbs S hS
  have e1 : lrd E = Real.log ((discr E).natAbs : ℝ) / Module.finrank ℚ E := by
    unfold lrd
    rw [rootDiscr_def, Real.log_rpow (by exact_mod_cast abs_pos.2 (discr_ne_zero E)), Nat.cast_natAbs]
    field_simp
  rw [e1, le_div_iff₀ hn, Finset.sum_mul]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun q _ => ?_) h
  unfold different_vp
  push_cast
  field_simp

theorem different_nonneg (E : Type) [Field E] [NumberField E] (q : ℕ) : (0 : ℝ) ≤ (different_vp E q : ℝ) := by
  unfold different_vp
  push_cast
  positivity

theorem primeSum_add (E : Type) [Field E] [NumberField E] {S B : Finset ℕ} {e : ℕ → ℝ} {s a : ℝ} (h : PrimeSum S e s)
    (hB : ∀ q ∈ B, q.Prime) (ha : 0 ≤ a) :
    PrimeSum (S ∪ B) (fun q => e q + if q ∈ B then a * (different_vp E q : ℝ) + 1 else 0) (s + (a * lrd E + logSum B)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun q hq => (Finset.mem_union.1 hq).elim (h1 q) (hB q), fun q => add_nonneg (h2 q) ?_, fun q hq => ?_, ?_⟩
  · have := different_nonneg E q
    split_ifs
    · positivity
    · exact le_rfl
  · rw [Finset.mem_union, not_or] at hq
    simp [h3 q hq.1, hq.2]
  · simp only [add_mul, Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · rw [← Finset.sum_subset Finset.subset_union_left fun q _ hq => by rw [h3 q hq, zero_mul]]
      exact h4
    · rw [← Finset.sum_subset Finset.subset_union_right fun q _ hq => by rw [if_neg hq, zero_mul]]
      rw [Finset.sum_congr rfl fun q hq => show (if q ∈ B then a * (different_vp E q : ℝ) + 1 else 0) * Real.log q =
        a * ((different_vp E q : ℝ) * Real.log q) + Real.log q by rw [if_pos hq]; ring,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      exact add_le_add (mul_le_mul_of_nonneg_left (sum_different_le E B hB) ha) le_rfl

theorem size_le {f r l n m d σ c : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hl : 1 ≤ l) (hm0 : 0 ≤ m) (hm : 2 * m ≤ n)
    (hn : n ≤ 20 * f * r ^ 2) (hd : d ≤ 3 * l) (hc : 0 ≤ c) (hσ : σ ≤ c * (f * r * l)) :
    m * (f * r) * d + σ ≤ (30 + c) * (f * r * l) ^ 12 := by
  have hz : 1 ≤ f * r * l := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hr) hl
  have h1 : f * r * l ≤ (f * r * l) ^ 12 := le_self_pow₀ hz (by norm_num)
  have h3 : (f * r * l) ^ 3 ≤ (f * r * l) ^ 12 := pow_le_pow_right₀ hz (by norm_num)
  have h4 : f ^ 2 * r ^ 3 * l ≤ f ^ 3 * r ^ 3 * l ^ 3 :=
    mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hf (by norm_num)) (by positivity))
      (le_self_pow₀ hl (by norm_num)) (by positivity) (by positivity)
  have h5 : m * (f * r) * d ≤ m * (f * r) * (3 * l) := mul_le_mul_of_nonneg_left hd (by positivity)
  have h6 : m * (f * r * (3 * l)) ≤ 10 * f * r ^ 2 * (f * r * (3 * l)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h7 := mul_le_mul_of_nonneg_left h1 hc
  nlinarith

end GlobalTheory.RefSum.ToWeight

end
