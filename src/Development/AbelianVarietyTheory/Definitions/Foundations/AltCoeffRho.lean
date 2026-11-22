import Mathlib
import Formalism.DegreeFormula.FlagDegFormula

noncomputable section
open MvPolynomial Finset

namespace GlobalTheory.FlagHook

def rho (N : ℕ) : Fin N → ℕ := fun c => N - 1 - (c : ℕ)

end GlobalTheory.FlagHook
