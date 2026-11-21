import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt

namespace ReciprocityTheory.AnForm.P

open MeasureTheory Metric
open scoped ContDiff

noncomputable section

def polyMaxOff {D : ℕ} (S : Finset (Fin D)) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (t : ℝ) : ℝ :=
  sSup (φ '' (closedBall z t \ ReciprocityTheory.AnForm.A.coordDiv S))

end

end ReciprocityTheory.AnForm.P
