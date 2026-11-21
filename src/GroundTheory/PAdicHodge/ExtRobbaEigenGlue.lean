import Mathlib
import GroundTheory.PAdicHodge.ExistsWeightLeOfConvergesAt
import GroundTheory.PAdicHodge.ExtRobbaDMRankOne

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

end TeichLift

end GroundTheory.PAdicHodge

namespace GroundTheory.PAdicHodge

namespace TeichLift

end TeichLift

end GroundTheory.PAdicHodge

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob)

def powRad {σ : Set.Ioo (0 : ℝ) 1} (r : Set.Ioc (0 : ℝ) σ) : Set.Ioc (0 : ℝ) (F.powRadius σ) :=
  ⟨(r : ℝ) ^ p ^ F.a, pow_pos r.2.1 _, pow_le_pow_left₀ r.2.1.le r.2.2 _⟩

@[simp] theorem coe_powRad {σ : Set.Ioo (0 : ℝ) 1} (r : Set.Ioc (0 : ℝ) σ) :
    ((F.powRad r : Set.Ioc (0 : ℝ) (F.powRadius σ)) : ℝ) = (r : ℝ) ^ p ^ F.a := rfl

def powRadRoot {τ : Set.Ioo (0 : ℝ) 1} (r : Set.Ioc (0 : ℝ) (F.rootRadius τ)) : Set.Ioc (0 : ℝ) τ :=
  ⟨(r : ℝ) ^ p ^ F.a, pow_pos r.2.1 _, by
    have h := pow_le_pow_left₀ r.2.1.le r.2.2 (p ^ F.a)
    have e : ((F.rootRadius τ : Set.Ioo (0 : ℝ) 1) : ℝ) ^ p ^ F.a = τ :=
      congrArg Subtype.val (F.powRadius_rootRadius τ)
    exact h.trans e.le⟩

@[simp] theorem coe_powRadRoot {τ : Set.Ioo (0 : ℝ) 1} (r : Set.Ioc (0 : ℝ) (F.rootRadius τ)) :
    ((F.powRadRoot r : Set.Ioc (0 : ℝ) τ) : ℝ) = (r : ℝ) ^ p ^ F.a := rfl

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
