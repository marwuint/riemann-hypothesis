import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.AigGen
import Development.WeilBound.CoreStatements.HodgeTatePoints.PfCoordOfSystem
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem genDeg_of_system (h : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement) :
    GenDegStatement :=
  _root_.PositivityTheory.HtPt.Aig.genDeg (_root_.PositivityTheory.HtPt.Aig.pfCoord h) fibreDim

end GlobalTheory.CompanionTheory.Ar.Giv
