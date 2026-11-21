import Formalism.GaussValuationBounds.GaussUnit

noncomputable section

namespace Formalism.NOK

open scoped ENNReal

open IsDiscreteValuationRing in
theorem minLeGaussValAdd : GaussAdd := by
  intro O _ _ _ x f g
  refine le_iInf fun n => ?_
  have h1 : min (gaussV x f) (gaussV x g) ≤
      min ((((addVal O (PowerSeries.coeff n f) : ℕ∞)) : ℝ≥0∞) + ENNReal.ofReal (x * n))
        ((((addVal O (PowerSeries.coeff n g) : ℕ∞)) : ℝ≥0∞) + ENNReal.ofReal (x * n)) :=
    min_le_min (iInf_le _ n) (iInf_le _ n)
  refine h1.trans ?_
  rw [min_add_add_right, map_add]
  gcongr ?_ + _
  have h2 := addVal_add (R := O) (a := PowerSeries.coeff n f) (b := PowerSeries.coeff n g)
  rcases le_total (addVal O (PowerSeries.coeff n f)) (addVal O (PowerSeries.coeff n g)) with h | h
  · rw [min_eq_left (ENat.toENNReal_le.mpr h)]
    exact ENat.toENNReal_le.mpr (by rwa [min_eq_left h] at h2)
  · rw [min_eq_right (ENat.toENNReal_le.mpr h)]
    exact ENat.toENNReal_le.mpr (by rwa [min_eq_right h] at h2)

open IsDiscreteValuationRing in
theorem gaussValC : GaussC := by
  intro O _ _ _ x _ c
  refine le_antisymm ((iInf_le _ 0).trans (by simp)) (le_iInf fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [PowerSeries.coeff_C, if_neg hn.ne', addVal_zero]
    simp

open IsDiscreteValuationRing in
theorem gaussValUnit : GaussUnit := by
  intro O _ _ _ x _ u hu
  obtain ⟨w, hw⟩ := hu.map (PowerSeries.constantCoeff (R := O))
  refine le_antisymm ((iInf_le _ 0).trans ?_) (by simp)
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hw, addVal_eq_zero_of_unit]
  simp

end Formalism.NOK
