import Mathlib

open NumberField

namespace ReciprocityTheory.Cheb

noncomputable section

abbrev NZIdeal (E : Type) [Field E] [NumberField E] : Type := {a : Ideal (𝓞 E) // a ≠ ⊥}

abbrev Prm (E : Type) [Field E] [NumberField E] : Type := IsDedekindDomain.HeightOneSpectrum (𝓞 E)

end

end ReciprocityTheory.Cheb
