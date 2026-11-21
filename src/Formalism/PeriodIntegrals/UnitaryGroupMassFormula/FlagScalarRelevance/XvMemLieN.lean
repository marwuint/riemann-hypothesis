import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds

noncomputable section

namespace PI.FRS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem xv_apply (x v y : S.V) : xv S x v y = S.hT v y • x - S.hT x y • v := rfl

end PI.FRS
