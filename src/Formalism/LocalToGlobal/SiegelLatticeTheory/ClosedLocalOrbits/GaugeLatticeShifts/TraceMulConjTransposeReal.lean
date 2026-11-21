import Formalism.LocalRingCardinality.DataCD

open Matrix

noncomputable section

namespace Formalism.MainNotions.S.Gauge.Cd

variable {P Q : ℕ}

local notation "ι" => Fin P ⊕ Fin Q

def hs2 (Z : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (Z i j)

end Formalism.MainNotions.S.Gauge.Cd
