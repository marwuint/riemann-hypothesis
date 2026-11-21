import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.LatticeFromNormOne

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW.Ind

open PI.KLW

def resL {K : Type} [Field K] {ι : Type} (i0 : ι) : (ι → K) →ₗ[K] ({i // i ≠ i0} → K) :=
  LinearMap.funLeft K K Subtype.val

theorem resL_apply {K : Type} [Field K] {ι : Type} (i0 : ι) (v : ι → K) (j : {i // i ≠ i0}) :
    resL i0 v j = v j.1 := rfl

end PI.KLW.Ind

namespace PI.KLW

end PI.KLW
