import Mathlib
import GroundTheory.PAdicHodge.SlopeRobbaPure
import GroundTheory.PAdicHodge.ExtRobbaEigenStep
import GroundTheory.PAdicHodge.ExtRobbaOrd
import GroundTheory.PAdicHodge.DMTeichPow
import GroundTheory.PAdicHodge.DMTeichBasic

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob) [CompleteSpace L]

def πEdag (T : TeichLift p L Γ) : T.Edag :=
  ⟨algebraMap Γ T.B T.π, T.Econ_le_Edag ⟨1 / 2, by norm_num, by norm_num⟩
    (T.algebraMap_π_mem_Econ _)⟩

theorem edagToTilde_πEdag : T.edagToTilde (πEdag T) = T.πTilde := rfl

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
