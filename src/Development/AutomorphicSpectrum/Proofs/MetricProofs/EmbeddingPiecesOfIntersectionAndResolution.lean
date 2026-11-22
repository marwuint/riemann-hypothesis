import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPiecesAdditive
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolution
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem embeddingPieces_of_resK (hA : ArithIntersectionSystemStatement)
    (hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) :
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.Statement :=
  have hInt : PtsIntegrableStatement := _root_.GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK hR
  have hRes : ResExistsStatement := _root_.GlobalTheory.CompanionTheory.Ar.Giv.resExists_of_resK hR
  GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.PiecesAdditive.proof hInt)
    (_root_.GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree hA hRes hInt)

end GlobalTheory.CompanionTheory.Ar.Giv
