import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.PlaceShiftModel

open NumberField IsDedekindDomain GlobalTheory.CompHt GlobalTheory.HTLat

variable {E : Type} [Field E] [NumberField E] {ℓ : ℕ} [Fact ℓ.Prime]

theorem norm_le_one (τ : E →+* ℂ_[ℓ]) (a : 𝓞 E) : ‖τ (a : E)‖ ≤ 1 := by
  rw [← algebraMap_embO (PadicComplexInt.integers ℓ) τ a]
  exact (GlobalTheory.PadicComplexHost.mem_iff_norm _ _).1 (Subtype.prop _)

theorem norm_ell : ‖(ℓ : ℂ_[ℓ])‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[ℓ] ℂ_[ℓ]), norm_algebraMap']
  exact Padic.norm_p_lt_one

end GlobalTheory.FlatCM.PlaceShiftModel

end
