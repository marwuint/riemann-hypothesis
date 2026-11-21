import Formalism.SharpRestriction.InertJacobiLevels.AsmRec

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

def ej (R : Ranks) (p : HCParam R) (j : ℕ) : ℝ := if h : j - 1 < R.m then ((p.e ⟨j - 1, h⟩ : ℚ) : ℝ) else 0

theorem wj_ej (D : D7) (j : ℕ) (τ : D.what₂.Tau) : wj D j τ = ej D.R (D.hc τ) j := rfl

end Formalism.MainNotions.Inhab

end
