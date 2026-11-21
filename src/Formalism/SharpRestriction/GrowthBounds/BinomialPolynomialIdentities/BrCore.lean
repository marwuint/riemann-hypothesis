import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ABridge
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcColESymmVal
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.InducedSectionsSpanStatement
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.RationalBitableauLatticeStatement

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

section B9
theorem global_sections_schur (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.GlobalSectionsSchur D := fun n _ mu R _ _ hR =>
  Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_one n mu R hR
end B9

section lowerOffDiagonalCoeff
theorem bracket_polynomial_span (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.BracketPolynomialSpan D := fun n _ mu hmu =>
  Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_two n mu hmu
end lowerOffDiagonalCoeff

end Formalism.MainNotions.G.ColumnFamilies
