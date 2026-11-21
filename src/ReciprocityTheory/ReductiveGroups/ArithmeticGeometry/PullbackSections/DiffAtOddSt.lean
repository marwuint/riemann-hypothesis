import Mathlib

noncomputable section

open NumberField UniqueFactorizationMonoid

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

def DiffExpSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (ℓ a m : ℕ), ℓ.Prime → ¬ ℓ ∣ m →
    (discr E).natAbs = ℓ ^ a * m →
    ∀ P : Ideal (𝓞 E), P.IsPrime → (ℓ : 𝓞 E) ∈ P →
      (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P * Module.finrank ℚ E =
        a * (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).count P

end ReciprocityTheory.ChartRestriction.G.PullbackSections
