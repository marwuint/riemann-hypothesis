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

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
