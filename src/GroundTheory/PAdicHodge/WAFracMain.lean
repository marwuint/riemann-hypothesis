import Mathlib
import GroundTheory.PAdicHodge.WABridgeApprox
import GroundTheory.PAdicHodge.WAFracOrbit
import GroundTheory.PAdicHodge.BCrisRegularFinal
import GroundTheory.PAdicHodge.AnnNormAcrisToAnnPosBig
import GroundTheory.PAdicHodge.WAFracAnn
import GroundTheory.PAdicHodge.ToUntiltFieldEqZeroIff
import GroundTheory.PAdicHodge.ExtRobbaRoot
import GroundTheory.PAdicHodge.FundamentalSeqSurj
import GroundTheory.PAdicHodge.BCrisPlusInvariants
import GroundTheory.PAdicHodge.FontaineLemmaInvariants
import GroundTheory.PAdicHodge.WAFracFrobAnn
import GroundTheory.PAdicHodge.ExistsNormLeOfNormLtOneFinite
import GroundTheory.PAdicHodge.WAFracAnnCris
import GroundTheory.PAdicHodge.ExtRobbaBezout

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WAFrac

open Laurent Filter Topology UniformSpace
open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris WABridge WAPeriodT

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔽" => frob ℂ_[p] p

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

end WAFrac

end GroundTheory.PAdicHodge
