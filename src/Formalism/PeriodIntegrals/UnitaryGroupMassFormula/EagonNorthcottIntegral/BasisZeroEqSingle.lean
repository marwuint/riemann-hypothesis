import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.YHom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.DivisionPartitionTotal

noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial

private lemma noX_iff {D : ℕ} (f : P D) : NoX f ↔ ∃ g, rename Sum.inr g = f := Iff.rfl

private lemma isZL_iff {D a j : ℕ} (ω : W D) : IsZL a j ω ↔
    (((∀ J, J.card ≠ j → ω J = 0) ∧ ∀ J, YHom a (ω J)) ∧ K ys ω = 0) ∧ ∀ J, NoX (ω J) := Iff.rfl

end PI.EagonNorthcottZ
