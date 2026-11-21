import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open UpperHalfPlane ModularGroup ModularForm Complex NumberField
open scoped Real Modular MatrixGroups nonZeroDivisors

section Ties

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

end Ties

end GroundTheory.Heights₂.Theta
