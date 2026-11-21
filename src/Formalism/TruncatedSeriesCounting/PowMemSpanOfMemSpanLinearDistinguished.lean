import Mathlib
import Formalism.WindowSums.Statement
import Formalism.GaussValuationBounds.Statement

noncomputable section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

open PowerSeries

def KapWin : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (χ : ℤ_[ℓ]ˣ), PadicInt.valuation ((χ : ℤ_[ℓ]) - 1) = 1 →
    ∀ (ell K D : ℕ) (a : Fin K → ℤ) (L : Fin K → ℕ) (JJ : Finset ℤ),
      JJ ⊆ Finset.univ.biUnion (fun k => Finset.Ico (a k) (a k + (L k : ℤ))) →
      (∀ i ∈ JJ, |i| ≤ (D : ℤ)) →
      (Formalism.WindowSums.PP ℓ χ ell JJ).eval 1 ≠ 0 ∧
      (PadicInt.valuation ((Formalism.WindowSums.PP ℓ χ ell JJ).eval 1) : ℝ) ≤
        (ell : ℝ) + ((∑ k, L k : ℕ) : ℝ) * (1 + ell) +
          ∑ k, ((L k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D)

def ColTwoStep : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (ℓ g g₀ e e' : ℕ)
    (Z I : Submodule O M) (s s₀ : Finset M),
    I ≤ Z → s.card ≤ g → s₀.card ≤ g₀ → (↑s₀ : Set M) ⊆ Z →
    Submodule.span O (s : Set M) ⊔ I = Z →
    (∀ p ∈ Z, (ℓ ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) →
    (∀ p ∈ Submodule.span O (s₀ : Set M), (ℓ ^ e' : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      ((g * e + g₀ * e' : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds
