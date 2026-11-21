import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem ptsIntegrable_of_resK :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → PtsIntegrableStatement :=
  fun h => GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists (_root_.GlobalTheory.CompanionTheory.Ar.Giv.resExists_of_resK h)

end GlobalTheory.CompanionTheory.Ar.Giv
