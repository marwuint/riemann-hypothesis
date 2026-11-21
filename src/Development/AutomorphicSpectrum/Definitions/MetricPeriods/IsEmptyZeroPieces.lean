import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SimilitudeFactorFormGroupBoundedOfTestSupport
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AffineChartParamCoverProjectiveLine
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GramSignatureTwoOneEntryZeroZero

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.PieceModel

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P MeasureTheory GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open GlobalTheory.CompanionTheory.Ar.PB.LineModel

instance uniqueLow : Unique (LowEnt Unit 2) where
  default := ((), ⟨(1, 0), by decide⟩)
  uniq := by decide

end GlobalTheory.CompanionTheory.Ar.Cmp.PieceModel
