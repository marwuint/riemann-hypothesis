import Mathlib
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.FormalDegreeBessel.StatementRP

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open scoped ENNReal ComplexOrder

noncomputable section

namespace GlobalTheory.HCXi.LineStabiliser

variable (k r' : ℕ)

def fst : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩

theorem e0_eq : e0 k r' = Pi.single (fst k r') 1 := rfl

end GlobalTheory.HCXi.LineStabiliser
