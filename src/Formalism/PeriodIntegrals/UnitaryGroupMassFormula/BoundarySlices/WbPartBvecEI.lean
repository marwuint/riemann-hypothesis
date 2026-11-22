import Formalism.FormalDegreeBessel.StatementBF
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix

noncomputable section

namespace PI.HermitianEmbeddingSlice

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic

variable {k r : ℕ}

def dd (k : ℕ) (j : Fin (k + 1)) : ℂ := if j = Fin.last k then -1 else 1

end PI.HermitianEmbeddingSlice
