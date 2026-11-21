import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.ZuckTensor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DualDefs

open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

section Conj
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Cj.continuous_mk : Continuous (Cj.mk : H → Cj H) := continuous_id

variable {n : ℕ}

theorem sigC_mk (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) (x : H) :
    sigC σ g (Cj.mk x) = Cj.mk (σ (revM g) x) := rfl

end Conj

end PI.ZuckTensorWork
end
