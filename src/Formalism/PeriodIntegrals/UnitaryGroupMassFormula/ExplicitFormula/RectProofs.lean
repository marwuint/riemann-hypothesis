import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.RectIntEqZeroOfDifferentiableOn

namespace PI.EF

open Complex

theorem rectResidue : RectResidue := by
  intro x₀ x₁ y₀ y₁ H Z wt e u hu h1 h2 h3 h4 hH hZ
  exact Rect.rect_residue (z := ⟨x₀, y₀⟩) (w := ⟨x₁, y₁⟩) Z wt e hu
    ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩ hH
    (fun ρ hρ => ⟨(hZ ρ hρ).1, (hZ ρ hρ).2⟩)

end PI.EF
