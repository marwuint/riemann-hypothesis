import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesCoefficientsCuspidal : Prop := GlobalTheory.Dec.CoefCusp

end GlobalTheory.Published
