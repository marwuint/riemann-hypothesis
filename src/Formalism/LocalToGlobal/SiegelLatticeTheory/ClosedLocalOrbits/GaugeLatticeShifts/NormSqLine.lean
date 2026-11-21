import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj

noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL

section Pos

variable {n r k : ℕ} (ε : Fin n → Bool)

def hJL (x : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun v := hJ ε x v
  map_add' v w := UnitaryIsometries.hJ_add_right ε x v w
  map_smul' a v := by simp [UnitaryIsometries.hJ_smul_right]

end Pos

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
