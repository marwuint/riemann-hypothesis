import Mathlib
import GroundTheory.PAdicHodge.AnnNormAcrisToAnnPosBig
import GroundTheory.PAdicHodge.ExtRobbaEigenStep

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace WAFrac

open Laurent Filter Topology UniformSpace
open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris WAPeriodT

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔽" => frob ℂ_[p] p

variable (p) (ρ1 : Set.Ioo (0 : ℝ) 1)

abbrev inRad : Set.Ioc (0 : ℝ) ρ1 := (𝔽).radPow ρ1

variable {p}

theorem annIoc_annOut : annIoc (annOut ρ1 (inRad p ρ1)) = topRad ρ1 := rfl

theorem annIoc_annIn : annIoc (annIn ρ1 (inRad p ρ1)) = (𝔽).radPow ρ1 := rfl

end WAFrac

end GroundTheory.PAdicHodge
