import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaEigenGlue
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem convAll_invSelf : T.ConvAll (IsLocalization.Away.invSelf T.π) := fun ρ _ _ => by
  rw [coeffB_invSelf]; exact convergesAt_pi_single _ _ _

namespace TeichFrob

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob) {n : ℕ}

def radPow (ρ : Set.Ioo (0 : ℝ) 1) : Set.Ioc (0 : ℝ) ρ :=
  ⟨(F.powRadius ρ : ℝ), (F.powRadius ρ).2.1, F.powRadius_le_self ρ⟩

variable {F}

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge

namespace GroundTheory.PAdicHodge

namespace TeichLift

namespace TeichFrob

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
