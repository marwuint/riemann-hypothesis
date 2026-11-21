import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallPacking
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory
  Topology

noncomputable section

namespace ArithmeticVolumeResolution

variable {ι0 : Type} [Fintype ι0]

theorem error_isLittleO (D : ℕ) (K₁ K₂ : ℝ) :
    (fun n : ℕ => K₁ * (n : ℝ) ^ D + K₂ * ((n : ℝ) ^ D * Real.log n)) =o[atTop] pw D := by
  have h1 : (fun n : ℕ => (n : ℝ) ^ D) =o[atTop] pw D := by
    have := (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (Nat.lt_succ_self D)).comp_tendsto
      tendsto_natCast_atTop_atTop
    exact this
  have h2 : (fun n : ℕ => (n : ℝ) ^ D * Real.log n) =o[atTop] pw D := by
    have := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop).mul_isLittleO
      (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop)
    refine this.congr_right fun n => ?_
    simp [pw, pow_succ]
  exact (h1.const_mul_left K₁).add (h2.const_mul_left K₂)

end ArithmeticVolumeResolution

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
