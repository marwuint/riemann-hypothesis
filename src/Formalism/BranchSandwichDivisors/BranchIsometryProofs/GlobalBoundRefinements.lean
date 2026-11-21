import Mathlib
import Formalism.QuotientMetricDivisors.StatementK
import Formalism.BranchSandwichDivisors.StatementR
import Formalism.BranchSandwichDivisors.StatementL
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.TransferMean
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Transfer
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.MapScale
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Interlace
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.GoodDual

open Finset Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.BranchingDeterminantCap

namespace VacLev

theorem hyp1 : (LinearMap.id : ℚ →ₗ[ℚ] ℚ) ∘ₗ LinearMap.id = LinearMap.id := rfl
end VacLev

namespace PlaceVacuity

def swapL : ℚ × ℚ →ₗ[ℚ] ℚ × ℚ := (LinearEquiv.prodComm ℚ ℚ ℚ).toLinearMap

def Pc : Submodule ℚ (Fin 2 → ℚ × ℚ) :=
  LinearMap.eqLocus (LinearMap.proj 1) (swapL.comp (LinearMap.proj 0))

theorem mem_Pc (φ : Fin 2 → ℚ × ℚ) : φ ∈ Pc ↔ φ 1 = (φ 0).swap := Iff.rfl

end PlaceVacuity

end Formalism.BranchingDeterminantCap
