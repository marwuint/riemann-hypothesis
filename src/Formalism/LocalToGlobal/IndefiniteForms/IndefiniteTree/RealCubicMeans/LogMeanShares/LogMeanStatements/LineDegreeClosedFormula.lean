import Mathlib

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.NormVectorIdentities.Items

variable (K : Type) [Field K] [NumberField K]

def degLineS (nFin : HeightOneSpectrum (𝓞 K) → ℝ) (nInf : (K →+* ℂ) → ℝ) : ℝ :=
  -((∑ᶠ la, Real.log (nFin la)) + ∑ σ : K →+* ℂ, Real.log (nInf σ)) / (Module.finrank ℚ K : ℝ)

end Formalism.NormVectorIdentities.Items
