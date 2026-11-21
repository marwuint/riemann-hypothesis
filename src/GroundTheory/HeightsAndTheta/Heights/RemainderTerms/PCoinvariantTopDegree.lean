import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem Coinv.psumIdeal_rat_eq (f N : ℕ) :
    Coinv.psumIdeal ℚ f N =
      Ideal.span {P | ∃ k τ, 1 ≤ k ∧ k ≤ N ∧ P = blockPowerSum f N k τ} := rfl

end

end GroundTheory.Heights₂.Heights.RestTerms
