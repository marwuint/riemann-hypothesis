import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyChern
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Proportionality

open Filter Topology Finset

noncomputable section

structure CauchyPolyFamily (n D : ℕ) where

  F : ℝ → MvPolynomial (Fin n) ℝ

  δ : ℝ → ℝ

  R : ℝ
  degree_le : ∀ t, 0 < t → t ≤ 1 → (F t).totalDegree ≤ D
  δ_tendsto : Tendsto δ (𝓝[>] 0) (𝓝 0)
  R_pos : 0 < R
  cauchy : ∀ t t' (lam : Fin n → ℝ), 0 < t' → t' ≤ t → t ≤ 1 → ‖lam‖ ≤ R →
    |MvPolynomial.eval lam (F t) - MvPolynomial.eval lam (F t')| ≤ δ t

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Proportionality
