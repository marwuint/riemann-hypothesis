import Formalism.PeriodIntegrals.PhMeasCore

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI.PhMeasCore.UnitaryGroupMassFormula

open PI.PhMeasCore

def MulOnUH {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Hm : Matrix (Fin n) (Fin n) ℂ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  σ 1 = 1 ∧ ∀ a ∈ UH Hm, ∀ b ∈ UH Hm, σ (a * b) = (σ a).comp (σ b)

end PI.PhMeasCore.UnitaryGroupMassFormula

end
