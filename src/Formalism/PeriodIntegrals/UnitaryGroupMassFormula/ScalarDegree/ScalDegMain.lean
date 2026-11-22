import Mathlib
import Formalism.PeriodIntegrals.ScalDeg

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScalDeg

open MvPolynomial PI.ScalDeg

def gv {T : Type} {N N' : ℕ} (s : T → ℂ) (y' : T → Matrix (Fin N') (Fin N') ℂ) (k : FrV T N) :
    MvPolynomial (Idx T N N') ℂ :=
  ∑ b : Fin N', C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
    X ((k.1, b, k.2.1) : Idx T N N')

end PI.UnitaryGroupMassFormula.ScalDeg
