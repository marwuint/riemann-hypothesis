import Formalism.NormUnitaryBounds.Statement

open MvPolynomial Finset

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas.NU

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def cnt {d : ℕ} (t : Fin d → σ) : σ →₀ ℕ := ∑ m, Finsupp.single (t m) 1

def fct (e : σ →₀ ℕ) : ℕ := ∏ i, (e i).factorial

def T (d : ℕ) (F : MvPolynomial σ ℂ) (t : Fin d → σ) : ℂ :=
  coeff (cnt t) F * (fct (cnt t) : ℂ) / (d.factorial : ℂ)

end Formalism.NormUnitaryCountingLemmas.NU

namespace Formalism.NormUnitaryCountingLemmas

end Formalism.NormUnitaryCountingLemmas
