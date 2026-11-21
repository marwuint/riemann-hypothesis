import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaDMForward
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

namespace TeichLift

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem gaussNorm_π_pow (c : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) :
    ConvergesAt (T.coeffB (algebraMap Γ T.B T.π ^ c)) ρ ∧
      gaussNorm (T.coeffB (algebraMap Γ T.B T.π ^ c)) ρ = ρ ^ c := by
  rw [← map_pow, T.coeffB_algebraMap, zcoeff_π_pow, gaussNorm_pi_single _ _ hρ0]
  exact ⟨convergesAt_pi_single _ _ _, by simp⟩

namespace TeichFrob

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
