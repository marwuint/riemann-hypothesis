import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormEmbeddingIntegerLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousExtensionAdicCompletion

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain TensorProduct Formalism.L2.DIV

namespace GlobalTheory.AdeleEv

variable {l : ℕ} [Fact l.Prime]

theorem norm_int_le {E : Type} [Field E] [NumberField E] (τ : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖τ x‖ ≤ 1 := by
  obtain ⟨v, hv⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l τ
  by_contra h
  have h0 : (x : E) ≠ 0 := by
    rintro h0
    rw [h0, map_zero, norm_zero] at h
    exact h zero_le_one
  have h1 : ‖τ (x : E)⁻¹‖ < 1 := by
    rw [map_inv₀, norm_inv]
    exact inv_lt_one_of_one_lt₀ (not_le.1 h)
  have h2 := (hv _).2 h1
  rw [map_inv₀] at h2
  have h3 : v.valuation E (x : E) ≤ 1 := v.valuation_le_one x
  have h4 : v.valuation E (x : E) ≠ 0 := (map_ne_zero _).2 h0
  exact absurd ((inv_lt_one₀ (zero_lt_iff.2 h4)).1 h2) (not_lt.2 h3)

end GlobalTheory.AdeleEv

end
