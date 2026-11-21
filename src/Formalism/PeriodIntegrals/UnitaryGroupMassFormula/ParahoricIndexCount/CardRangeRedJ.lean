import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ParahoricIndexCount.ThetaInjective

noncomputable section

open Matrix Formalism.DoubleCosetMeasures.P.GLRed

namespace PI.ParahoricIdxZ.W

section B

variable {F : Type} [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O)

theorem mk_eq_zero {u : F} (hu : u ∈ O) (o : F) (ho : o ∈ O) (h : u = ϖ * o) :
    Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨u, hu⟩ : O) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨⟨o, ho⟩, Subtype.ext (by simp [h, mul_comm])⟩

end B

end PI.ParahoricIdxZ.W
