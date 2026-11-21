import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers

noncomputable section
namespace GlobalTheory.NT.Model
open NumberField IsDedekindDomain GlobalTheory.NT

private theorem mulSupport_heckeVal_pow_count_finite {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : (L ≃ₐ[K] L) →* ℂˣ) {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    (Function.mulSupport fun 𝔭 : HeightOneSpectrum (𝓞 K) =>
      heckeVal L χ 𝔭 ^ (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors).Finite := by
  refine (Ideal.finite_factors hI).subset fun 𝔭 h => ?_
  simp only [Function.mem_mulSupport] at h
  have h0 : (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors ≠ 0 := fun h0 => h (by rw [h0, pow_zero])
  exact (Associates.count_ne_zero_iff_dvd hI 𝔭.irreducible).mp h0

section Cyc
open IsCyclotomicExtension.Rat

variable {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem heckeIdeal_mul (χ : (L ≃ₐ[K] L) →* ℂˣ) {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0) :
    heckeIdeal L χ (I * J) = heckeIdeal L χ I * heckeIdeal L χ J := by
  unfold heckeIdeal
  rw [← finprod_mul_distrib (mulSupport_heckeVal_pow_count_finite L χ hI) (mulSupport_heckeVal_pow_count_finite L χ hJ)]
  refine finprod_congr fun 𝔭 => ?_
  rw [← Associates.mk_mul_mk, Associates.count_mul (Associates.mk_ne_zero.mpr hI)
    (Associates.mk_ne_zero.mpr hJ) (Associates.irreducible_mk.mpr 𝔭.irreducible), pow_add]

theorem heckeIdeal_prime (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔮 : HeightOneSpectrum (𝓞 K)) :
    heckeIdeal L χ 𝔮.asIdeal = heckeVal L χ 𝔮 := by
  unfold heckeIdeal
  rw [finprod_eq_single _ 𝔮 fun 𝔭 h => ?_]
  · rw [Associates.count_self (Associates.irreducible_mk.mpr 𝔮.irreducible), pow_one]
  · have hne : Associates.mk 𝔭.asIdeal ≠ Associates.mk 𝔮.asIdeal := fun heq =>
      h (IsDedekindDomain.HeightOneSpectrum.ext
        (associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp heq)))
    rw [Associates.count_eq_zero_of_ne (Associates.irreducible_mk.mpr 𝔭.irreducible)
      (Associates.irreducible_mk.mpr 𝔮.irreducible) hne, pow_zero]

theorem heckeIdeal_top (χ : (L ≃ₐ[K] L) →* ℂˣ) : heckeIdeal L χ 1 = 1 := by
  unfold heckeIdeal
  rw [Associates.mk_one, Associates.factors_one]
  refine finprod_eq_one_of_forall_eq_one fun 𝔭 => ?_
  rw [Associates.count_zero (Associates.irreducible_mk.mpr 𝔭.irreducible), pow_zero]

variable (m : ℕ) [NeZero m] (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {m} ℚ F]

end Cyc

end GlobalTheory.NT.Model
end
