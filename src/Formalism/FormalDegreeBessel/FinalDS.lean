import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSLowK
import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSFdeg
import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSRatio

namespace Formalism.QuantumDeterminants

theorem fdegPos : FdegPos := formal_degree_pos_holds
theorem fdegRatio : FdegRatio := formalDegreeShiftRatio_holds
theorem capelliHW : CapelliHW := capelliHighestWeight_holds
end Formalism.QuantumDeterminants
