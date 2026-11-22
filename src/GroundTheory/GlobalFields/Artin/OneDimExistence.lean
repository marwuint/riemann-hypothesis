import Mathlib
import GroundTheory.GlobalFields.Artin.OneDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField

noncomputable section

section FiniteOrder

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)

theorem isOfFinOrder_heckeCharacterOfChar : IsOfFinOrder (heckeCharacterOfChar χ) := by
  refine isOfFinOrder_iff_pow_eq_one.2
    ⟨Nat.card (charField χ ≃ₐ[K] charField χ), Nat.card_pos, ContinuousMonoidHom.ext fun c ↦ ?_⟩
  rw [ContinuousMonoidHom.pow_apply]
  change toCircleHom (charBar χ) (reciprocityMap K (charField χ) c) ^ _ = 1
  rw [← map_pow, pow_card_eq_one', map_one]

end FiniteOrder

end

end GroundTheory.Global
