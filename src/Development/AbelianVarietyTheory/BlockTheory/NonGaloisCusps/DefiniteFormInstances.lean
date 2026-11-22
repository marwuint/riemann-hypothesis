import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFormInstances

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

section Concl

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (B : NBC A)

def SphericalInert (j : ℕ) (π : B.AU j) : Prop := ∀ w : PlE H, ¬ IsSplitPl H w → B.sphAU j π w

end Concl

end GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFormInstances
