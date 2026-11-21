import Mathlib
import GroundTheory.PAdicHodge.KerFontaineThetaCompFrobeniusEquivSymmPow
set_option maxSynthPendingDepth 1

noncomputable section

open WittVector Filter Topology

namespace GroundTheory.PAdicHodge

namespace AInf

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪♭" => PreTilt (normInteger K) p

theorem isAdicComplete_p : IsAdicComplete (Ideal.span {(p : AInf K p)}) (AInf K p) :=
  inferInstance

local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

end AInf

end GroundTheory.PAdicHodge
