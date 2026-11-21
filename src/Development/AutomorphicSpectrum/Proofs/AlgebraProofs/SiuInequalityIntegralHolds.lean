import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.OfRemaining
import Development.WeilBound.CoreStatements.HodgeTatePoints.KleimanInputUniverseZero
import Development.WeilBound.CoreStatements.HodgeTatePoints.KTwins
import Development.WeilBound.CoreStatements.HodgeTatePoints.SiuKodaira
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem siuZ : SiuZStatement := by
  have hR4 := _root_.PositivityTheory.HtPt.Kra.kleiman_input_universe_zero
  obtain ⟨-, hVA, hSC⟩ := _root_.PositivityTheory.HtPt.Ktw.k_twins hR4
  exact GroundTheory.Heights₂.Heights.ForSecondHalf.SiuZB.of_kodaira (_root_.PositivityTheory.HtPt.Siua.siu_kodaira hVA hSC)

end GlobalTheory.CompanionTheory.Ar.Giv
