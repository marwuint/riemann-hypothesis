import Formalism.HermitianCurvature.HermitianCurvatureProofs.L1QuotientIntegralBound

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem ag_lt_a {k r : ℕ} {h : ℝ} (hG : GapOK k r h) : AG k r < aOf r h := by
  have h1 := hG.2.2.2
  have h2 := ag_nonneg k r
  have h3 : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  linarith

end Formalism.FourierDecayAlt.P.S3dx4
