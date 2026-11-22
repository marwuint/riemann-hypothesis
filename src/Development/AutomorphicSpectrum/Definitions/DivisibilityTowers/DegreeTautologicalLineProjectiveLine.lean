import Mathlib
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.DegreeFormula.PointDegree.PowSum
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

noncomputable section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.Top.Model

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem degFl_eq (F : RP Ψ N) : degFl F = Formalism.DegreeFormula.degFl Ψ N F := rfl
theorem linRoot_eq (lam : Wt Ψ N) : linRoot lam = Formalism.DegreeFormula.linRoot lam := rfl
theorem pk_eq (τ : Ψ) (k : ℕ) : (pk τ k : RP Ψ N) = GlobalTheory.FlagPoly.pSum τ k := rfl
theorem degFl_pk_mul (τ : Ψ) (k : ℕ) (hk : 1 ≤ k) (Q : RP Ψ N) : degFl (pk τ k * Q) = 0 := Formalism.DegreeFormula.PPowSum.degFlPowerSum Ψ N τ k Q hk

theorem degFl_add (P Q : RP Ψ N) : degFl (P + Q) = degFl P + degFl Q := by
  simp only [degFl, coeff_add, mul_add, Finset.sum_add_distrib]

end GlobalTheory.CompanionTheory.Ar.Top.Model
