import Mathlib
import Formalism.DegreeFormula.FlagDegFormula

open MvPolynomial Formalism.DegreeFormula

noncomputable section

namespace GlobalTheory.FlagPoly

abbrev Pol (ι : Type) (N : ℕ) : Type := MvPolynomial (ι × Fin N) ℝ

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

def pSum (τ : ι) (k : ℕ) : Pol ι N := ∑ i : Fin N, X (τ, i) ^ k

def pLow (j : ℕ) (τ : ι) (k : ℕ) : Pol ι N :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), X (τ, i) ^ k

def shF (j : ℕ) (τ : ι) (F : Pol ι N) : ℝ :=
  degFl ι N (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), pderiv (τ, i) F)

def totF (τ : ι) (F : Pol ι N) : ℝ := degFl ι N (∑ i : Fin N, pderiv (τ, i) F)

def ev (lam : ι → Fin N → ℝ) (P : Pol ι N) : ℝ := eval (fun x => lam x.1 x.2) P

def dimGr (ι : Type) [Fintype ι] (N j : ℕ) : ℕ := Fintype.card ι * (j * (N - j))

end GlobalTheory.FlagPoly
