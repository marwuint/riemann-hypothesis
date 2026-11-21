import Mathlib
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

noncomputable section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.Top.Model

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem dimFl_eq : dimFl Ψ N = Formalism.DegreeFormula.dimFl Ψ N := rfl
theorem degFl_eq (F : RP Ψ N) : degFl F = Formalism.DegreeFormula.degFl Ψ N F := rfl
theorem linRoot_eq (lam : Wt Ψ N) : linRoot lam = Formalism.DegreeFormula.linRoot lam := rfl
theorem flagDeg_eq (lam : Wt Ψ N) : flagDeg lam = Formalism.DegreeFormula.flagDeg Ψ N lam := rfl
theorem pk_eq (τ : Ψ) (k : ℕ) : (pk τ k : RP Ψ N) = GlobalTheory.FlagPoly.pSum τ k := rfl
theorem pkLow_eq (j : ℕ) (τ : Ψ) (k : ℕ) : (pkLow j τ k : RP Ψ N) = GlobalTheory.FlagPoly.pLow j τ k := rfl
theorem Sh_eq (j : ℕ) (τ : Ψ) (F : RP Ψ N) : Sh j τ F = GlobalTheory.FlagPoly.shF j τ F := rfl
theorem Tot_eq (τ : Ψ) (F : RP Ψ N) : Tot τ F = GlobalTheory.FlagPoly.totF τ F := rfl

theorem degFl_pk_mul (τ : Ψ) (k : ℕ) (hk : 1 ≤ k) (Q : RP Ψ N) : degFl (pk τ k * Q) = 0 :=
  Formalism.DegreeFormula.degreePowerSumMulEqZero Ψ N τ k Q hk

theorem degFl_add (P Q : RP Ψ N) : degFl (P + Q) = degFl P + degFl Q := by
  simp only [degFl, coeff_add, mul_add, Finset.sum_add_distrib]

end GlobalTheory.CompanionTheory.Ar.Top.Model
