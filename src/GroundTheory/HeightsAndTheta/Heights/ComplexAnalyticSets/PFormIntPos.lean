import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjective
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogSmul
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterOsgood

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm
open scoped ContDiff

noncomputable section

namespace FormIntegralPositivity

variable {n : ℕ}

theorem analyticAt_sheet {d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) :
    AnalyticAt ℂ s (A *ᵥ x) := by
  obtain ⟨U, hU, hxU, hsU, -⟩ := hs
  rw [analyticAt_pi_iff]
  intro i
  exact ReciprocityTheory.ChartRestriction.G.Geo.osgood d U (fun y => s y i) hU
    (fun y hy => differentiableWithinAt_pi.mp (hsU y hy) i) (A *ᵥ x) hxU

end FormIntegralPositivity

end

end GroundTheory.Heights₂.Heights
