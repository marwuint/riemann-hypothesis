import Formalism.DoubleCosetMeasures.Statement

noncomputable section

open MeasureTheory

namespace Formalism.DoubleCosetMeasures.P

section Generic

variable {X : Type}

def cls (r : Setoid X) (q : Quotient r) : Set X := Quotient.mk r ⁻¹' {q}

theorem mem_cls {r : Setoid X} {q : Quotient r} {y : X} :
    y ∈ cls r q ↔ Quotient.mk r y = q := Iff.rfl

variable [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end Generic

end Formalism.DoubleCosetMeasures.P
