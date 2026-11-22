import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraAlt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfNear
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraBis
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitelyGeneratedModPow

namespace UpperTheory.V.Lib.Small

theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := UpperTheory.Reformulated.B.S6.norm_le_one_of_isIntegral l x hx

end UpperTheory.V.Lib.Small
