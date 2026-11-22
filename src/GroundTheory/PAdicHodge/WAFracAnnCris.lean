import Mathlib
import GroundTheory.PAdicHodge.WAFracAnn
import GroundTheory.PAdicHodge.WAPeriodT
import GroundTheory.PAdicHodge.BCrisNewtonApprox
import GroundTheory.PAdicHodge.ACrisGalois
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

end TeichLift

namespace WAFrac

open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)

variable (ρ0 : Set.Ioo (0 : ℝ) 1) (σ0 : Set.Ioc (0 : ℝ) ρ0)

variable {ρ0 σ0}

variable (hσ : (p : ℝ)⁻¹ ≤ σ0)
include hσ

end WAFrac

end GroundTheory.PAdicHodge
