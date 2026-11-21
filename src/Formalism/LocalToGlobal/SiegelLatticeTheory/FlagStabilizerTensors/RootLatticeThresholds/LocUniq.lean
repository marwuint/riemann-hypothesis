import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.Pf.WuDec

section Core

variable {k r : ℕ}

theorem lowSmoothSK {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {w : H}
    (hds : IsDSHpk k r ε lam σ) (hlow : IsLowUnitH k r ε lam σ w) : w ∈ smoothVecs (k := k) (r := r) σ :=
  Formalism.L2.SG.Pf.k_finite_smooth k r ε lam H σ hds w (PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow)

end Core

end Formalism.L2.SG.Pf.WuDec
