import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.FormalDegreeBessel.StatementG
import Formalism.FormalDegreeBessel.StatementBF
import Formalism.FormalDegreeBessel.StatementDS

noncomputable section

namespace PI.BesselL2FixAtZero

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff ENNReal
open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Defs

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def ellA (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r) : ℂ :=
  if h : a.val + 1 < r then g (Formalism.QuantumDeterminants.eI k r a) (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩)
  else (g *ᵥ z) (Formalism.QuantumDeterminants.eI k r a)

def psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  Complex.exp (Complex.I * ((∑ a, c a * ellA k r z g a).re : ℂ))

end Defs

end PI.BesselL2FixAtZero
