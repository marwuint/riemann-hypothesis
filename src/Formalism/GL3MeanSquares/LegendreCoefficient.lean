import Mathlib
import Formalism.FormalGroupWitt.Statement

noncomputable section

namespace Formalism.HermitianLattices.ExpSeriesBivariate

open Finset

def expS {σ K : Type} [Field K] [Algebra ℚ K] (f : MvPowerSeries σ K) : MvPowerSeries σ K :=
  PowerSeries.subst f (PowerSeries.exp K)

def InLam {σ K : Type} [NormedField K] [Algebra ℚ K] (f : MvPowerSeries σ K) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ Formalism.G.IntegralMv (expS f)

def IntegralInverse : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (σ : Type) [Fintype σ] [DecidableEq σ]
    (T : σ → MvPowerSeries σ K) (J' : Matrix σ σ K),
    (∀ i, MvPowerSeries.constantCoeff (T i) = 0) → (∀ i, Formalism.G.IntegralMv (T i)) →
    (∀ i j, ‖J' i j‖ ≤ 1) →
    (Matrix.of fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (T i)) * J' = 1 →
    ∃ X' : σ → MvPowerSeries σ K, (∀ i, MvPowerSeries.constantCoeff (X' i) = 0) ∧
      (∀ i, Formalism.G.IntegralMv (X' i)) ∧ (∀ i, MvPowerSeries.subst X' (T i) = MvPowerSeries.X i) ∧
      ∀ i, MvPowerSeries.subst T (X' i) = MvPowerSeries.X i

end Formalism.HermitianLattices.ExpSeriesBivariate
