import Mathlib
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLimDeg

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical

noncomputable section

namespace GlobalTheory.Mean4

open GlobalTheory.FlagPoly GlobalTheory.FlagAr

variable {D : D7} (Y : ShimX D.what₂.Tau)

abbrev Wt : Type := D.what₂.Tau → Fin Y.N → ℝ

abbrev Fn : Type := Pol D.what₂.Tau Y.N →ₗ[ℝ] ℝ

structure SlopeTestRemainingChoices where

  dir : Wt Y

  w : Y.Comp → ℝ

  Ps : ℝ → Y.Comp → MvPolynomial (Option (D.what₂.Tau × Fin Y.N)) ℝ

  ht : Y.ALB → Y.Pt → ℝ

  dense : Y.Comp → Set Y.Pt → Prop

variable {Y} (A : SlopeTestRemainingChoices Y) (Φ : ℝ → Fn Y) (hh : Fn Y)

end GlobalTheory.Mean4
