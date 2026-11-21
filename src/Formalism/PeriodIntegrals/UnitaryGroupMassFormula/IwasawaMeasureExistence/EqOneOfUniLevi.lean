import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.AntiLevWittJ

noncomputable section

namespace PI.IwaMeasEx.LP

open Matrix Formalism.L2.S.S7.WittLeviSubgroups PI.IwaMeasEx.PD

section Form

variable {R : Type} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin n) (lev : ι → ℕ)
  {Fm Fi : Matrix (Fin n) (Fin n) R}

theorem cT_apply (σ : R →+* R) {m p : Type} (M : Matrix m p R) (i : p) (j : m) :
    Formalism.UG.cT σ M i j = σ (M j i) := rfl

variable (hFm : Fm * Fi = 1) (hFi : Fi * Fm = 1) {g : GL (Fin n) R} (hg : g ∈ parGL (cols e Fm) lev)

end Form

end PI.IwaMeasEx.LP

end
