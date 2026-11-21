import Mathlib

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace GlobalTheory

section Multiplicity

variable {G X : Type*} [Group G] [MulAction G X]

variable [MeasurableSpace X] {μ : Measure X} [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G] {B D : Set X}

omit [MeasurableSpace X] [MeasurableConstSMul G X] [Countable G] in

@[to_additive
]
theorem tsum_indicator_smul_eq_encard (B : Set X) (x : X) :
    ∑' g : G, ((fun y => g • y) ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) x
      = ({g : G | g • x ∈ B}.encard : ℝ≥0∞) := by
  rw [← ENNReal.tsum_set_one, tsum_subtype {g : G | g • x ∈ B} (fun _ => (1 : ℝ≥0∞))]
  refine tsum_congr fun g => ?_
  by_cases h : g • x ∈ B <;> simp [Set.indicator, h]

@[to_additive
]
theorem sum_restrict_preimage_smul_le (hB : NullMeasurableSet B μ) {m : ℝ≥0∞}
    (hm : ∀ᵐ x ∂μ.restrict D, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    (Measure.sum fun g : G => (μ.restrict D).restrict ((fun y => g • y) ⁻¹' B))
      ≤ m • μ.restrict D := by
  have hB' : ∀ g : G, NullMeasurableSet ((fun y => g • y) ⁻¹' B) (μ.restrict D) := fun g =>
    (hB.preimage (measurePreserving_smul g μ).quasiMeasurePreserving).mono
      Measure.restrict_le_self
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.sum_apply _ hA, Measure.smul_apply, smul_eq_mul]
  have h1 : ∀ g : G, ((μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) A
      = ∫⁻ x in A, ((fun y => g • y) ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) x
          ∂(μ.restrict D) := by
    intro g
    rw [lintegral_indicator₀ ((hB' g).mono Measure.restrict_le_self), setLIntegral_one,
      Measure.restrict_apply hA,
      Measure.restrict_apply₀ ((hB' g).mono Measure.restrict_le_self), inter_comm]
  simp_rw [h1]
  rw [← lintegral_tsum fun g => (aemeasurable_const.indicator₀
    ((hB' g).mono Measure.restrict_le_self))]
  simp_rw [tsum_indicator_smul_eq_encard]
  calc ∫⁻ x in A, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ∂(μ.restrict D)
      ≤ ∫⁻ _ in A, m ∂(μ.restrict D) := lintegral_mono_ae (ae_restrict_of_ae hm)
    _ = m * (μ.restrict D) A := by rw [setLIntegral_const]

@[to_additive setLIntegral_le_mul_of_ae_covers_vadd
]
theorem setLIntegral_le_mul_of_ae_covers (hD : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    {m : ℝ≥0∞} (hm : ∀ᵐ x ∂μ.restrict D, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ := by
  have hcov : B ≤ᵐ[μ] (⋃ g : G, g • (((fun y => g • y) ⁻¹' B) ∩ D) : Set X) := by
    filter_upwards [hD] with x ⟨g, hg⟩ hx
    refine mem_iUnion.2 ⟨g⁻¹, g • x, ⟨?_, hg⟩, by simp⟩
    change g⁻¹ • g • x ∈ B
    rw [inv_smul_smul]
    exact hx
  have hB' : ∀ g : G, NullMeasurableSet ((fun y => g • y) ⁻¹' B) (μ.restrict D) := fun g =>
    (hB.preimage (measurePreserving_smul g μ).quasiMeasurePreserving).mono
      Measure.restrict_le_self
  calc ∫⁻ x in B, u x ∂μ
      ≤ ∫⁻ x in ⋃ g : G, g • (((fun y => g • y) ⁻¹' B) ∩ D), u x ∂μ :=
        lintegral_mono_set' hcov
    _ ≤ ∑' g : G, ∫⁻ x in g • (((fun y => g • y) ⁻¹' B) ∩ D), u x ∂μ := lintegral_iUnion_le _ _
    _ = ∑' g : G, ∫⁻ x, u x ∂((μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) := by
        refine tsum_congr fun g => ?_
        rw [Measure.restrict_restrict₀ (hB' g), ← image_smul,
          ← (measurePreserving_smul g μ).setLIntegral_comp_emb (measurableEmbedding_const_smul g)]
        simp only [hu]
    _ = ∫⁻ x, u x ∂(Measure.sum fun g : G =>
          (μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) := (lintegral_sum_measure _ _).symm
    _ ≤ ∫⁻ x, u x ∂(m • μ.restrict D) :=
        lintegral_mono' (sum_restrict_preimage_smul_le hB hm) le_rfl
    _ = m * ∫⁻ x in D, u x ∂μ := by rw [lintegral_smul_measure, smul_eq_mul]

omit [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] in

@[to_additive ae_encard_vadd_mem_le_one
]
theorem ae_encard_smul_mem_le_one (hD : IsFundamentalDomain G D μ) :
    ∀ᵐ x ∂μ, {g : G | g • x ∈ D}.encard ≤ 1 := by
  have h : ∀ᵐ x ∂μ, ∀ g₁ g₂ : G, g₁ ≠ g₂ → x ∉ g₁ • D ∩ g₂ • D := by
    refine ae_all_iff.2 fun g₁ => ae_all_iff.2 fun g₂ => ?_
    by_cases h : g₁ = g₂
    · simp [h]
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hD.aedisjoint h)] with x hx _ using hx
  filter_upwards [h] with x hx
  rw [encard_le_one_iff]
  intro a b ha hb
  by_contra hab
  refine hx a⁻¹ b⁻¹ (by simpa using hab) ⟨?_, ?_⟩
  · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact ha
  · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact hb

@[to_additive setLIntegral_le_of_isAddFundamentalDomain_of_ae_covers
]
theorem setLIntegral_le_of_isFundamentalDomain_of_ae_covers {D' : Set X}
    (hD : IsFundamentalDomain G D μ) (hD' : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D')
    {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in D, u x ∂μ ≤ ∫⁻ x in D', u x ∂μ := by
  have := setLIntegral_le_mul_of_ae_covers hD' hD.nullMeasurableSet hu (m := 1) (by
    filter_upwards [ae_restrict_of_ae (ae_encard_smul_mem_le_one hD)] with x hx
    exact_mod_cast ENat.toENNReal_le.2 hx)
  simpa using this

@[to_additive measure_le_of_isAddFundamentalDomain_of_ae_covers
]
theorem measure_le_of_isFundamentalDomain_of_ae_covers {D' : Set X}
    (hD : IsFundamentalDomain G D μ) (hD' : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D') : μ D ≤ μ D' := by
  simpa using setLIntegral_le_of_isFundamentalDomain_of_ae_covers hD hD' (u := fun _ => 1)
    (fun _ _ => rfl)

end Multiplicity

end GlobalTheory
