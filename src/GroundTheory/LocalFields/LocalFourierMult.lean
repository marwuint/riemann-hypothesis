import Mathlib
import GroundTheory.LocalFields.LocalFourierPadic

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology
open scoped NNReal ENNReal

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

instance borelSpace_units : BorelSpace Kˣ :=
  measurableEmbedding_units_val.borelSpace isOpenEmbedding_units_val.isInducing

def unitsMeasureOf (μ : Measure K) : Measure Kˣ :=
  Measure.comap Units.val (μ.withDensity fun x => ((modulus x : ℝ≥0∞))⁻¹)

def multHaarOf (μ : Measure K) : Measure Kˣ := multHaarConst K • unitsMeasureOf μ

theorem multHaarOf_haarIntegers : multHaarOf (haarIntegers K) = multHaar K := by
  rw [multHaarOf, unitsMeasureOf, multHaar, Measure.comap_smul]

omit [BorelSpace K] in
theorem unitsMeasureOf_smul (c : ℝ≥0∞) (μ : Measure K) :
    unitsMeasureOf (c • μ) = c • unitsMeasureOf μ := by
  rw [unitsMeasureOf, unitsMeasureOf, withDensity_smul_measure, Measure.comap_smul]

omit [BorelSpace K] in
theorem multHaarOf_smul (c : ℝ≥0∞) (μ : Measure K) : multHaarOf (c • μ) = c • multHaarOf μ := by
  rw [multHaarOf, multHaarOf, unitsMeasureOf_smul, smul_comm]

theorem multHaarOf_eq (μ : Measure K) [μ.IsAddHaarMeasure] :
    multHaarOf μ = μ (𝒪[K] : Set K) • multHaar K := by
  conv_lhs => rw [eq_smul_haarIntegers μ]
  rw [multHaarOf_smul, multHaarOf_haarIntegers]

instance (μ : Measure K) [μ.IsAddHaarMeasure] : (multHaarOf μ).IsHaarMeasure := by
  rw [multHaarOf_eq μ]
  have h0 : μ (𝒪[K] : Set K) ≠ 0 := by
    rw [← coe_valBall_zero]
    exact (isOpen_valBall 0).measure_ne_zero μ ⟨0, zero_mem _⟩
  have ht : μ (𝒪[K] : Set K) ≠ ∞ := by
    rw [← coe_valBall_zero]
    exact (isCompact_valBall 0).measure_lt_top.ne
  exact IsHaarMeasure.smul _ h0 ht

namespace Padic

end Padic

end GroundTheory.LocalField
