import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.StatementsGluing
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.LocallyFreeSpreadHyp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

section Join

variable {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type}

theorem joinPt_eq_segreJoin (x : ι → Ω) (z : κ → Ω') :
    joinPt x z = segreJoin (fun i => algebraMap Ω Ω' (x i)) z := rfl

theorem pullbackLat_eq_pullLat {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} {x : ι → Ω}
    (B : ChartBundle ℤ x r E) (z : κ → Ω') (q : ι × κ) :
    pullbackLat B z q = IndefiniteRowSideFullHecke.Antisym.pullLat x z B.lat q := rfl

end Join

end GroundTheory.Heights₂.Heights
