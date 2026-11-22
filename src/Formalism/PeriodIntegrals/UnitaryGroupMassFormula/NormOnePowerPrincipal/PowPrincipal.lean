import Mathlib

open NumberField nonZeroDivisors

namespace NormOnePowProof

variable {E : Type} [Field E] [NumberField E]

theorem map_integral (c : E →+* E) (y : 𝓞 E) : IsIntegral ℤ (c (y : E)) :=
  (RingOfIntegers.isIntegral_coe y).map c.toIntAlgHom

noncomputable def σ (c : E →+* E) (y : 𝓞 E) : 𝓞 E := ⟨c (y : E), map_integral c y⟩

end NormOnePowProof
