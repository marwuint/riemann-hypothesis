import Mathlib
import GroundTheory.LocalFields.Different
import GroundTheory.LocalFields.LocalFourierExistence

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel
open scoped nonZeroDivisors

attribute [local instance high] FaithfulSMul.to_isTorsionFree

section Dual

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

end Dual

section TraceChar

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable (L) in

def traceChar (ψ : AddChar K Circle) : AddChar L Circle :=
  ψ.compAddMonoidHom (Algebra.trace K L).toAddMonoidHom

theorem trace_algebraMap_mul (a : K) (x : L) :
    Algebra.trace K L (algebraMap K L a * x) = a * Algebra.trace K L x := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

variable [ValuativeRel K] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L]

variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1

variable [Algebra.IsSeparable K L]

end TraceChar

end GroundTheory.LocalField
