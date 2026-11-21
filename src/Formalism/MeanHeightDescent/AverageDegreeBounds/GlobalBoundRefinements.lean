import Mathlib
import Formalism.MeanHeightDescent.MuMaxMinkowski
import Formalism.MeanHeightDescent.BadRowsNumeric
import Formalism.MeanHeightDescent.CombinedAverageDegreeBound
import Formalism.QuotientMetricDivisors.StatementK
import Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeAssemblyHolds
import Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeFullAssemblyHolds
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq
import Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin
import Formalism.MeanHeightDescent.AverageDegreeBounds.TwistLower
import Formalism.MeanHeightDescent.AverageDegreeBounds.MuMaxMinkowski

namespace Formalism.ExtensionFiltration

noncomputable section Short
open Module NumberField
open Formalism.HN

section Core
open NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped ENNReal NNReal nonZeroDivisors

theorem mk_lt (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : InfinitePlace K → ℝ) (hg : ∀ w, 0 < g w)
    (h : (FractionalIdeal.absNorm I.1 : ℝ) * (2:ℝ) ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| <
      Real.pi ^ nrComplexPlaces K * ∏ w, g w ^ 2) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ ∀ w : InfinitePlace K, w a < g w := by
  classical
  let f : InfinitePlace K → NNReal := fun w => (g w).toNNReal
  have hmx : ∀ i, max (g i) 0 = g i := fun i => max_eq_left (hg i).le
  have hr : nrRealPlaces K = 0 := by
    unfold nrRealPlaces
    rw [Fintype.card_eq_zero_iff, isEmpty_subtype]
    exact fun w => not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
  have hm : ∀ w : InfinitePlace K, mult w = 2 := fun w => by
    unfold mult
    rw [if_neg (not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w))]
  have hd : Module.finrank ℝ (mixedSpace K) = 2 * nrComplexPlaces K := by
    rw [mixedEmbedding.finrank, ← card_add_two_mul_card_eq_rank, hr, zero_add]
  have hL : minkowskiBound K I ≠ ⊤ := by
    first
    | exact (minkowskiBound_lt_top K I).ne
    | exact (minkowskiBound_lt_top (K := K) (I := I)).ne
  have hR : volume (convexBodyLT K f) ≠ ⊤ := by
    rw [convexBodyLT_volume]
    simp
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (ENNReal.prod_ne_top fun w _ => ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have key : minkowskiBound K I < volume (convexBodyLT K f) := by
    rw [← ENNReal.toReal_lt_toReal hL hR, convexBodyLT_volume]
    unfold minkowskiBound
    rw [volume_fundamentalDomain_fractionalIdealLatticeBasis, volume_fundamentalDomain_latticeBasis, hd]
    simp [hm, hr, convexBodyLTFactor, f, hmx]
    rw [ENNReal.toReal_ofReal (by first | exact_mod_cast FractionalIdeal.absNorm_nonneg _ | positivity),
      Int.norm_eq_abs]
    have e : ∀ N s : ℝ, N * (((2:ℝ) ^ nrComplexPlaces K)⁻¹ * s) * (2:ℝ) ^ (2 * nrComplexPlaces K) =
        N * 2 ^ nrComplexPlaces K * s := by
      intro N s
      have h2 : (2:ℝ) ^ nrComplexPlaces K ≠ 0 := by positivity
      rw [two_mul, pow_add]
      calc N * (((2:ℝ) ^ nrComplexPlaces K)⁻¹ * s) * ((2:ℝ) ^ nrComplexPlaces K * (2:ℝ) ^ nrComplexPlaces K)
          = N * (2:ℝ) ^ nrComplexPlaces K * s *
              (((2:ℝ) ^ nrComplexPlaces K)⁻¹ * (2:ℝ) ^ nrComplexPlaces K) := by ring
        _ = N * 2 ^ nrComplexPlaces K * s := by rw [inv_mul_cancel₀ h2, mul_one]
    rw [e]
    first | exact h | linarith [h]
  obtain ⟨a, ha, ha0, hlt⟩ := exists_ne_zero_mem_ideal_lt K I key
  exact ⟨a, ha, ha0, fun w => lt_of_lt_of_eq (hlt w) (Real.coe_toNNReal _ (hg w).le)⟩

end Core

end Short

end Formalism.ExtensionFiltration
