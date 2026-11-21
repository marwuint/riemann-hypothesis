import Mathlib
import Formalism.DegreeFormula.FlagDegFormula

noncomputable section
open MvPolynomial Finset

namespace GlobalTheory.FlagHook

def altCoeff {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (n : ι → Fin N → ℕ)
    (P : MvPolynomial (ι × Fin N) ℝ) : ℝ :=
  (-1) ^ Formalism.DegreeFormula.dimFl ι N * ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) *
    P.coeff (Finsupp.equivFunOnFinite.symm (fun x : ι × Fin N => n x.1 (σ x.1 x.2)))

def rho (N : ℕ) : Fin N → ℕ := fun c => N - 1 - (c : ℕ)

theorem altCoeff_rho {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (P : MvPolynomial (ι × Fin N) ℝ) :
    altCoeff (fun _ => rho N) P = Formalism.DegreeFormula.degFl ι N P := rfl

end GlobalTheory.FlagHook
