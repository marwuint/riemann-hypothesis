import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesUpqExists : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ),
    (StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((N : ℝ) - 1) / 2 = (m : ℝ)) →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)),
      CompleteSpace H ∧ Nontrivial H ∧
      IsURepOn {g | gᴴ * Jm ε * g = Jm ε} σ ∧
      IsIrredOn {g | gᴴ * Jm ε * g = Jm ε} σ ∧
      (∀ v w : H, MemLp (coefOn (ε := ε) σ v w) 2 (muG ε)) ∧
      (∃ S : Submodule ℂ H, IsKTypeOf ε σ (lam + rhoN ε - rhoC ε) S) ∧
      ∀ (μ : Fin N → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
        nsq (lam + rhoN ε - rhoC ε + (2 : ℝ) • rhoC ε) ≤ nsq (μ + (2 : ℝ) • rhoC ε)

theorem discreteSeriesUpqExists_iff_dsExists : DiscreteSeriesUpqExists ↔ GlobalTheory.Dec.DSExists := Iff.rfl

end GlobalTheory.Published
