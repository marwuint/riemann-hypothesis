import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmStatements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open NumberField

section Ties

instance fact_sevenQ : Fact (∀ r : ℚ, r ^ 2 ≠ -7 + 0 * r) :=
  ⟨fun r h => by nlinarith [sq_nonneg r]⟩

abbrev QuadraticFieldSqrtNegSeven : Type := QuadraticAlgebra ℚ (-7) 0

instance : Algebra.IsQuadraticExtension ℚ QuadraticFieldSqrtNegSeven :=
  ⟨QuadraticAlgebra.finrank_eq_two _ _⟩

instance : NumberField QuadraticFieldSqrtNegSeven where

end Ties

end GroundTheory.Heights₂.Theta
