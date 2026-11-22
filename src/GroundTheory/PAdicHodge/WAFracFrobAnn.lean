import Mathlib
import GroundTheory.PAdicHodge.AnnNormAcrisToAnnPosBig

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

variable {p}

end WAFrac

end GroundTheory.PAdicHodge
