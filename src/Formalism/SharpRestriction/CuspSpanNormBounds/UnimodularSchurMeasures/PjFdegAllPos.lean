import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.UnimodF
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionConvolutionIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyProjectorSectionLocal

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

abbrev muInf (X : CData) : Measure X.I.Ginf := Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)

end Formalism.MainNotions.LeviCoordinates

end
