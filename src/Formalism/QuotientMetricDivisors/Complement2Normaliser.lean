import Mathlib
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LogFactorialIndices.StatementSize

open Module NumberField IsDedekindDomain Finset

noncomputable section

namespace Formalism.DivisionValues

def PlOver {K : Type} [Field K] [NumberField K] (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  0 < vw w (g : K)

def PlOverCoprime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g g' : ℕ), Nat.Coprime g g' →
    ∀ w : HeightOneSpectrum (𝓞 K), ¬ (PlOver g w ∧ PlOver g' w)

end Formalism.DivisionValues
