import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant

noncomputable section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal Pointwise

namespace GlobalTheory.Cusp.Model

section Four

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def four (D : D7) : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral 4 ![false, false, true, true] 2 2

end Four

end GlobalTheory.Cusp.Model

end
