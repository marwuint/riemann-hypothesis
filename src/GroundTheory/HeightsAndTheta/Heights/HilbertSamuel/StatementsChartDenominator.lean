import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartDenominator.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (b : K → ℤ) (τ : ℕ) (s : Ω),
    s ∈ chartLatQ y b τ → ∃ n : ℕ, 1 ≤ n ∧ (n : Ω) * s ∈ chartLat y b τ

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
