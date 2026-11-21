import Mathlib

open NumberField Module
open scoped nonZeroDivisors

namespace GlobalTheory

theorem card_mul_rpow_prod_le_sum {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    (Fintype.card ι : ℝ) * (∏ i, z i) ^ ((Fintype.card ι : ℝ)⁻¹) ≤ ∑ i, z i := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) z (fun _ _ => by positivity)
    (by simp [hc.ne']) (fun i _ => hz i)
  rw [Real.finsetProd_rpow _ _ (fun i _ => hz i), ← Finset.mul_sum] at h
  calc _ ≤ (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)⁻¹ * ∑ i, z i) := by gcongr
    _ = _ := by field_simp

section General

variable {K : Type*} [Field K] [NumberField K]

theorem norm_eq_prod_complexEmbeddings (x : K) :
    ((Algebra.norm ℚ x : ℚ) : ℂ) = ∏ σ : K →+* ℂ, σ x := by
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ x]
  simp

theorem trace_eq_sum_complexEmbeddings (x : K) :
    ((Algebra.trace ℚ K x : ℚ) : ℂ) = ∑ σ : K →+* ℂ, σ x := by
  rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => rfl), ← trace_eq_sum_embeddings ℂ (K := ℚ) (x := x)]
  simp

theorem abs_norm_eq_prod_complexEmbeddings (x : K) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  rw [← norm_prod, ← norm_eq_prod_complexEmbeddings, Complex.norm_ratCast]

theorem finrank_mul_abs_norm_rpow_le_sum (x : K) :
    (finrank ℚ K : ℝ) * |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ ((finrank ℚ K : ℝ)⁻¹)
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ := by
  rw [abs_norm_eq_prod_complexEmbeddings, ← Embeddings.card K ℂ]
  exact card_mul_rpow_prod_le_sum _ fun _ => norm_nonneg _

theorem finrank_mul_abs_norm_rpow_le_sum_sq (x : K) :
    (finrank ℚ K : ℝ) * |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ (2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_abs_norm_rpow_le_sum (x ^ 2)
  simp only [map_pow, norm_pow, Rat.cast_pow, abs_pow] at h
  rwa [div_eq_mul_inv, Real.rpow_mul (abs_nonneg _), Real.rpow_two]

theorem one_le_abs_norm_of_isIntegral {x : K} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    1 ≤ |Algebra.norm ℚ x| := by
  have hn : IsIntegral ℤ (Algebra.norm ℚ x) := Algebra.isIntegral_norm ℚ hx
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hn
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, Algebra.norm_eq_zero_iff] at hm
    exact h0 hm
  rw [← hm, eq_intCast]
  exact_mod_cast Int.one_le_abs hm0

theorem absNorm_le_abs_norm_of_mem {J : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ J)
    (h0 : x ≠ 0) : FractionalIdeal.absNorm J ≤ |Algebra.norm ℚ x| := by
  have hJ : J ≠ 0 := by
    rintro rfl
    exact h0 ((FractionalIdeal.mem_zero_iff _).mp hx)
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ x * J⁻¹ ≤ 1 := by
    calc _ ≤ J * J⁻¹ := by
          gcongr
          exact FractionalIdeal.spanSingleton_le_iff_mem.mpr hx
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hI' : FractionalIdeal.spanSingleton (𝓞 K)⁰ x = I * J := by
    rw [hI, inv_mul_cancel_right₀ hJ]
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    exact h0 (FractionalIdeal.spanSingleton_eq_zero_iff.mp (by simpa using hI'))
  have h1 : (1 : ℚ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
  rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), hI', map_mul,
    FractionalIdeal.coeIdeal_absNorm]
  exact le_mul_of_one_le_left (FractionalIdeal.absNorm_nonneg _) h1

theorem finrank_mul_absNorm_rpow_le_sum_sq {J : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ J)
    (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ (2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  refine le_trans ?_ (finrank_mul_abs_norm_rpow_le_sum_sq x)
  have h1 : ((FractionalIdeal.absNorm J : ℚ) : ℝ) ≤ |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    exact_mod_cast absNorm_le_abs_norm_of_mem hx h0
  have h2 : (0 : ℝ) ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg J
  gcongr

variable (K) in

theorem dual_one_eq_inv_differentIdeal :
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
      = (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]

variable (K) in

theorem absNorm_inv_differentIdeal :
    FractionalIdeal.absNorm (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹
      = |(discr K : ℚ)|⁻¹ := by
  rw [map_inv₀, FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal K]
  simp

theorem finrank_mul_discr_rpow_le_sum_sq {x : K}
    (hx : x ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) * |(discr K : ℝ)| ^ (-2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_absNorm_rpow_le_sum_sq hx h0
  rw [absNorm_inv_differentIdeal] at h
  rw [neg_div, Real.rpow_neg (abs_nonneg _), ← Real.inv_rpow (abs_nonneg _)]
  simpa using h

theorem finrank_div_rootDiscr_sq_le_sum_sq {x : K}
    (hx : x ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) / rootDiscr K ^ 2 ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_discr_rpow_le_sum_sq hx h0
  rw [neg_div, Real.rpow_neg (abs_nonneg _), div_eq_inv_mul, Real.rpow_mul (abs_nonneg _),
    Real.rpow_two] at h
  rw [rootDiscr_def, div_eq_mul_inv]
  simpa using h

theorem finrank_mul_discr_rpow_le_sum_sq_of_mem_traceDual {x : K}
    (hx : x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K)) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) * |(discr K : ℝ)| ^ (-2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  refine finrank_mul_discr_rpow_le_sum_sq ?_ h0
  rw [← dual_one_eq_inv_differentIdeal, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one]
  exact hx

end General

section TotallyReal

variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]

omit [NumberField F] in
variable (F) in

theorem bijective_ofRealHom_comp :
    Function.Bijective (fun σ : F →+* ℝ => Complex.ofRealHom.comp σ) := by
  refine ⟨fun σ τ h => RingHom.ext fun x => ?_, fun φ => ?_⟩
  · simpa using RingHom.congr_fun h x
  · exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, RingHom.ext fun x => by simp⟩

variable (F) in

theorem card_realEmbeddings : Fintype.card (F →+* ℝ) = finrank ℚ F := by
  rw [← Embeddings.card F ℂ]
  exact Fintype.card_of_bijective (bijective_ofRealHom_comp F)

theorem trace_eq_sum_realEmbeddings (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ σ : F →+* ℝ, σ x := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, trace_eq_sum_complexEmbeddings, Complex.ofReal_sum]
  exact ((bijective_ofRealHom_comp F).sum_comp (fun φ => φ x)).symm

end TotallyReal

end GlobalTheory
