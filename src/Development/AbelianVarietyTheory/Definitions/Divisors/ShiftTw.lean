import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne

noncomputable section

namespace GlobalTheory.LKRes

variable {H : Type} [Group H]

def conv (K : Subgroup H) (f f' : H → ℂ) (x : H) : ℂ :=
  ∑ᶠ q : H ⧸ K, f (Quotient.out q) * f' ((Quotient.out q)⁻¹ * x)

end GlobalTheory.LKRes
