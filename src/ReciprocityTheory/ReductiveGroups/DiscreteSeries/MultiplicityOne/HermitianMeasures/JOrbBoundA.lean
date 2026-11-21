import Mathlib

noncomputable section

open MeasureTheory Module
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB

instance pairBorel (m : ℕ) : BorelSpace ((Fin m → ℂ) × ℝ) := Prod.borelSpace

instance pairHaar (m : ℕ) : (volume : Measure ((Fin m → ℂ) × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
