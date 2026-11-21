import Mathlib

open NumberField nonZeroDivisors

namespace PI.DIP.NormOne

variable {E : Type} [Field E] [NumberField E]

theorem map_integral (c : E →+* E) (y : 𝓞 E) : IsIntegral ℤ (c (y : E)) :=
  (RingOfIntegers.isIntegral_coe y).map c.toIntAlgHom

noncomputable def σ (c : E →+* E) (y : 𝓞 E) : 𝓞 E := ⟨c (y : E), map_integral c y⟩

theorem coe_σ (c : E →+* E) (y : 𝓞 E) : ((σ c y : 𝓞 E) : E) = c (y : E) := rfl

end PI.DIP.NormOne
