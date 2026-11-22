import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsSepClosedResidueFieldPowerSeriesComplex
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.YonedaAddNaturalityLeft

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct

namespace GlobalTheory.FormalInv

section Tests

open GlobalTheory.NCyc

def Ram : Type := PowerSeries ℂ

instance : CommRing Ram := inferInstanceAs (CommRing (PowerSeries ℂ))

instance : HenselianLocalRing Ram := henselian_powerSeries_complex

instance : IsSepClosed (ResidueField Ram) := isSepClosed_residueField_powerSeries_complex

instance : IsAdicComplete (maximalIdeal Ram) Ram := by
  change IsAdicComplete (maximalIdeal (PowerSeries ℂ)) (PowerSeries ℂ)
  rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance

instance : Algebra (PowerSeries ℂ) Ram := (PowerSeries.expand (R := ℂ) 2 two_ne_zero).toRingHom.toAlgebra

instance : IsLocalHom (algebraMap (PowerSeries ℂ) Ram) := by
  refine ⟨fun a ha => ?_⟩
  have h : IsUnit (PowerSeries.expand (R := ℂ) 2 two_ne_zero a) := ha
  rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply] at h ⊢
  rwa [PowerSeries.coeff_expand, if_pos (dvd_zero 2)] at h

instance : Module.Finite (PowerSeries ℂ) Ram := by
  let s : Ram := (PowerSeries.X : PowerSeries ℂ)
  refine Module.finite_def.2 (Submodule.fg_def.2 ⟨{1, s}, Set.toFinite _, eq_top_iff.2 fun a _ => ?_⟩)
  refine Submodule.mem_span_pair.2 ⟨PowerSeries.mk fun n => PowerSeries.coeff (R := ℂ) (2 * n) a,
    PowerSeries.mk fun n => PowerSeries.coeff (R := ℂ) (2 * n + 1) a, ?_⟩
  show @Eq (PowerSeries ℂ) (PowerSeries.expand (R := ℂ) 2 two_ne_zero _ * (1 : PowerSeries ℂ) +
    PowerSeries.expand (R := ℂ) 2 two_ne_zero _ * (PowerSeries.X : PowerSeries ℂ)) a
  refine PowerSeries.ext fun n => ?_
  rw [mul_one, map_add]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rcases k with _ | k
    · simp [PowerSeries.coeff_expand]
    · rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_expand,
        PowerSeries.coeff_expand, if_pos (by omega), if_neg (by omega), PowerSeries.coeff_mk, add_zero,
        show 2 * ((2 * k + 1 + 1) / 2) = 2 * k + 1 + 1 by omega]
  · rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_expand, PowerSeries.coeff_expand, if_neg (by omega),
      if_pos (by omega), PowerSeries.coeff_mk, zero_add, show 2 * (2 * k / 2) + 1 = 2 * k + 1 by omega]

attribute [local instance] henselian_powerSeries_complex isSepClosed_residueField_powerSeries_complex
  faithfulSMul_powerSeries_complex isAlgebraic_powerSeries_complex

end Tests

end GlobalTheory.FormalInv

end
