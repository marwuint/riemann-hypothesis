import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.InputsOfUse
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassPush
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GrassmannHeightZ2OfInputsAndZ2

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem grassmannian_height_bound_of_systems :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
        GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement := by
  intro hSys hU hBig hResK
  exact _root_.GlobalTheory.CompanionTheory.Ar.Giv.grassmann_height_Z2_of_push (inputs_of_use hSys hU hBig hResK) hSys
    (hsLinks_of_use hU hBig).2.2.1

end GlobalTheory.CompanionTheory.Ar.Giv
