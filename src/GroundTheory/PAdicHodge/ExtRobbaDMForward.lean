import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaDMRankOne

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

namespace TeichLift

end TeichLift

namespace TeichLift

namespace TeichFrob

end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem coeffB_zero_B : T.coeffB 0 = 0 := by
  rw [← map_zero (algebraMap Γ T.B), coeffB_algebraMap, (T.zcoeff_eq_zero_iff 0).2 rfl]

namespace TeichFrob

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
