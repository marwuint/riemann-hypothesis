import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPolynomial Formalism.L2.Pj

section Germ

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def addF (k : Type) [CommRing k] (d : ℕ) : Fin d → PS k 2 d :=
  fun j => MvPowerSeries.X ((0 : Fin 2), j) + MvPowerSeries.X ((1 : Fin 2), j)

end Germ

end Formalism.MainNotions.ModuliIntegralCharts.H1
