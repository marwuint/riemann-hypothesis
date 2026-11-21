import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.LeviForms.ProjLineChartTarget
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.LineModel

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P MeasureTheory Matrix
open scoped ComplexOrder

def flagTh (p : Unit × Fin 2) : LocPot (OnePoint ℂ) := if p.2 = 0 then fsPot else LocPot.ofFun fun _ => 0

instance uniqueHead : Unique {a : Fin 2 // (a : ℕ) < 1} where
  default := ⟨0, by decide⟩
  uniq a := Subtype.ext (Fin.ext (by have := a.2; simp; omega))

end GlobalTheory.CompanionTheory.Ar.PB.LineModel
