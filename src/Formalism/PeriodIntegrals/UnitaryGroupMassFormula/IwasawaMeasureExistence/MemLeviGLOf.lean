import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.ParabolicFundamentalDomain

noncomputable section

namespace PI.IwaMeasEx.PD

open Matrix Formalism.L2.S.S7.WittLeviSubgroups

section Gen

variable {R : Type} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin n)

def cols (Fm : Matrix (Fin n) (Fin n) R) (r : ι) : Fin n → R := fun i => Fm i (e r)

variable {e}

variable (lev : ι → ℕ)

end Gen

end PI.IwaMeasEx.PD

end
