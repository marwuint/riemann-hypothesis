import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.KernelEntryData
import Formalism.SharpRestriction.GlobalSchurBounds.FirstClaimLemmaTwoFourOfLemmaTwoThree
import Formalism.SharpRestriction.DesignExistsOfChoices
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormOnePowerPrincipal.PowPrincipal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalBasisAtPrime.MemPrimeComplIff

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric NumberField

theorem lamC_mem' {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ Qbar) :
    lamC lam x = lam ⟨x, h⟩ := by
  unfold lamC; rw [dif_pos h]

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric NumberField

instance instUltraCp (p : ℕ) [Fact p.Prime] : IsUltrametricDist ℂ_[p] :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicComplex.isNonarchimedean p)

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Columns

end Formalism.MainNotions.GL3Columns

namespace Formalism.MainNotions.GL3Theta

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Columns

end Formalism.MainNotions.GL3Columns

namespace Formalism.MainNotions.ShortIntervalPrimes

end Formalism.MainNotions.ShortIntervalPrimes
