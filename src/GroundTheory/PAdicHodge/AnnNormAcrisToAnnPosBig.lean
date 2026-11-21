import Mathlib
import GroundTheory.PAdicHodge.WAFracAnnCris
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WAFrac

open Laurent Filter Topology UniformSpace
open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)

variable {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0}

section Pos

variable (hσ : (p : ℝ)⁻¹ ≤ σ0)

def radInvP : Set.Ioc (0 : ℝ) ρ0 := ⟨(p : ℝ)⁻¹, inv_pos.2 (Nat.cast_pos.2 hp.out.pos), hσ.trans σ0.2.2⟩

theorem coe_radInvP : ((radInvP hσ : Set.Ioc (0 : ℝ) ρ0) : ℝ) = (p : ℝ)⁻¹ := rfl

end Pos

end WAFrac

end GroundTheory.PAdicHodge
