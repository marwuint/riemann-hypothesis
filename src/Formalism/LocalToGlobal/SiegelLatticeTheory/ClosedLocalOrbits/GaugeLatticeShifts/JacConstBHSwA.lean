import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHSwB

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

variable {k r : ℕ}

def LongWeylElementSquare : Prop := ∀ k r : ℕ, w0B k r * w0B k r = 1

end Formalism.L2.SG.Pf.BH.Sw
