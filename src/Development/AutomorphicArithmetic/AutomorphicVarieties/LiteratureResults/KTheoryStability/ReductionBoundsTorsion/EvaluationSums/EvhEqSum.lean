import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.EvaluationSums.SuccAboveSuccEqCons

noncomputable section

namespace PositivityTheory.KB.ChainCochainPairing

variable {G : Type} [Group G]

theorem cob_eq_dC {Y : Type} {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : cob F = dC F := rfl

end PositivityTheory.KB.ChainCochainPairing
