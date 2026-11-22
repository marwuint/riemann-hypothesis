import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub

noncomputable section

open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct

namespace GlobalTheory.CentTorus

variable {p : ℕ} [Fact p.Prime]

abbrev algF {G : HTGroup p} (P : Pair G) : Subalgebra G.F G.C := Algebra.adjoin G.F {(P.γ : G.C)}

end GlobalTheory.CentTorus
