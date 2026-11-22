import Mathlib
import GroundTheory.PAdicHodge.WAEval
import GroundTheory.PAdicHodge.ACrisBdRGalois
import GroundTheory.PAdicHodge.InstMulSemiringActionGalPlus
import GroundTheory.PAdicHodge.BCrisNewtonApprox

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WABridge

open _root_.WittVector WittTilt WAEval TeichLift PhiGamma Laurent

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)

variable (p) in

def radTwo : Set.Ioo (0 : ℝ) 1 := (frob ℂ_[p] p).rootRadius (rhoMid p)

end WABridge

end GroundTheory.PAdicHodge
