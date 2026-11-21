import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaUnits
import GroundTheory.PAdicHodge.SlopePhiModule
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

def piB : T.Bˣ := (IsLocalization.Away.algebraMap_isUnit T.π).unit

theorem piB_val : (T.piB : T.B) = algebraMap Γ T.B T.π := IsUnit.unit_spec _

namespace TeichFrob

end TeichFrob

variable [CompleteSpace L]

namespace TeichFrob

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
