import Mathlib
import Formalism.PeriodIntegrals.IsoDerivB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.ExistsOePerm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.ApplyAt0EqSum

open Finset

noncomputable section

namespace PI.IsoDerivBFintype

open PI.IsoDerivB

section expand

variable {T : Type} {N N' : ℕ} (s : T → ℂ) (y' : T → Matrix (Fin N') (Fin N') ℂ)

def gD : FrV T N → MvPolynomial (Idx T N N') ℂ := fun k => ∑ b : Fin N',
    MvPolynomial.C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
      MvPolynomial.X ((k.1, b, k.2.1) : Idx T N N')

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (tp : Lt → T) (nu : Lt → YoungDiagram)

end expand

end PI.IsoDerivBFintype
