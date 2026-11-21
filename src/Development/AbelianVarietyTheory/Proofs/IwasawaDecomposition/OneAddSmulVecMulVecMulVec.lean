import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt

namespace GlobalTheory.UnipKill

noncomputable section

open ReciprocityTheory.ChartRestriction.G.FD NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem cc_ofInt (x : 𝓞 E) : cc (x : E) = IsCMField.ringOfIntegersComplexConj E x := rfl

variable (G : Matrix (Fin N) (Fin N) E)

end

end GlobalTheory.UnipKill
