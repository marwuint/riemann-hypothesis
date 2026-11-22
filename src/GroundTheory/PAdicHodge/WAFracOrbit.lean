import Mathlib
import GroundTheory.PAdicHodge.WAPeriodT
import GroundTheory.PAdicHodge.WAEval
import GroundTheory.PAdicHodge.ACrisBdRGalois
import GroundTheory.PAdicHodge.InstMulSemiringActionGalPlus
import GroundTheory.PAdicHodge.BCrisNewtonApprox
import GroundTheory.PAdicHodge.CauchySeqOfIncrements
import GroundTheory.PAdicHodge.ExtRobbaTrivialV

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

end TeichLift

namespace WAFrac

open _root_.WittVector WittTilt PhiGamma TeichLift UniformSpace WAEval WAPeriodT Filter Topology

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p

theorem isPrimOne_frob {ξ : (𝓣).int} (hξ : (𝓣).IsPrimOne ξ) :
    (𝓣).IsPrimOne ⟨(frob ℂ_[p] p).φ ξ, (frob ℂ_[p] p).map_int _ ξ.2⟩ where
  coeff_zero_ne := by
    show (𝓣).coeff ((frob ℂ_[p] p).φ ξ) 0 ≠ 0
    rw [coeff_frob]; exact pow_ne_zero _ hξ.coeff_zero_ne
  norm_coeff_zero_lt := by
    show ‖(𝓣).coeff ((frob ℂ_[p] p).φ ξ) 0‖ < 1
    rw [coeff_frob, norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hξ.norm_coeff_zero_lt hp.out.ne_zero
  norm_coeff_one := by
    show ‖(𝓣).coeff ((frob ℂ_[p] p).φ ξ) 1‖ = 1
    rw [coeff_frob, norm_pow, hξ.norm_coeff_one, one_pow]

def frobPt (P : (𝓣).Pt) : (𝓣).Pt :=
  ⟨⟨(frob ℂ_[p] p).φ P.1, (frob ℂ_[p] p).map_int _ P.1.2⟩, isPrimOne_frob P.2⟩

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

end WAFrac

namespace TeichLift

end TeichLift

namespace WAFrac

open _root_.WittVector WittTilt PhiGamma TeichLift UniformSpace WAEval WAPeriodT Filter Topology

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

end WAFrac

end GroundTheory.PAdicHodge
