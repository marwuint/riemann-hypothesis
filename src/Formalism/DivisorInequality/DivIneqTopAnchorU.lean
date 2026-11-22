import Mathlib
import Formalism.QuotientMetricDivisors.RatHermLcvTwist
import Formalism.QuotientMetricDivisors.DualMu
import Formalism.QuotientMetricDivisors.StatementK
import Formalism.QuotientMetricDivisors.TheoremDivIneqRows
import Formalism.QuotientMetricDivisors.TheoremDivIneqRowsShift
import Formalism.MirabolicMackeyTheory.StatementT

open Module NumberField IsDedekindDomain Finset
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisorInequality

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.LatticeIndexTer (ph)

def HeightS : Prop :=
  ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb]
    (TT : Finset Pl) [DecidablePred (· ∈ TT)] (nr : ℕ)

    (hu hP mlam logT : ℝ) (hK : J → ℝ) (aT : Pl → ℝ) (logH : J → Pl → ℝ) (Ch nV L' : ℝ)

    (ν : J → Pl → Fin nr → ℝ)

    (x eps L b a rd La m f k N S η b' logOm : ℝ)

    (g0 : J → ℝ) (logK MainNotions : J → Emb → ℝ) (logOmτ : Pl → Emb → ℝ) (logth0 : Emb → ℝ)
    (logh logh' : J → ℝ) (v logg C2 Cth C4 c5 c6 CT C8 Ce : ℝ)

    (ev : ℝ) (bT nτ lam1 D0 D1 logc logxi : Pl → ℝ) (Cev : ℝ),

    hu = (-(∑ t ∈ TT, aT t * logT) +
        Ch * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La) +
      ∑ j, ((∑ ρ, ((∑ i, ph (ν j ρ i)) - (∑ i, ν j ρ i) * logOm) + Ch * f * N ^ 2 * (La + m ^ 3 * L)) -
        (∑ ρ, logH j ρ - Ch * f * nV ^ 2 * L')) →

    ∑ j, (∑ ρ, logH j ρ - Ch * f * nV ^ 2 * L') ≤ mlam →

    (∀ j s, logK j s ≤
      (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
      (Fintype.card Pl : ℝ) * g0 j * logth0 s +
      ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
        2 * MainNotions j s + (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) +
        (logh j + logh' j))) →
    (∀ j, hK j = (∑ s, logK j s) / (Fintype.card Emb : ℝ)) →
    (∀ τ, (∑ s, logOmτ τ s) / (Fintype.card Emb : ℝ) = logOm) →
    (∀ j s, MainNotions j s ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT) + Ce * f * N ^ 2 * logg) →
    (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ Cth * L →
    (∀ j, logh j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, logh' j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, 0 ≤ g0 j ∧ g0 j ≤ N ^ 2) →
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤ c5 * La) →
    (∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La) →
    logg ≤ C8 * L →
    0 ≤ C2 → 0 ≤ Cth → 0 ≤ C4 → 0 ≤ c5 → 0 ≤ c6 → 0 ≤ C8 → 0 ≤ Ce →

    hP ≤ -(∑ τ, nτ τ * logT) + ∑ τ, (2 * logc τ + logxi τ) + ev →
    (∀ τ, logc τ ≤ (N - 1) * D1 τ * Real.log (2 * a)) →
    (∀ τ, logxi τ ≤ N * (N - 1) / 2 * Real.log (2 * a)) →
    (∀ τ, nτ τ = lam1 τ - D0 τ) →
    (∀ τ ∈ TT, lam1 τ = aT τ - (N - k) / 2) → (∀ τ, τ ∉ TT → S - (N - 1) / 2 ≤ lam1 τ) →
    (∀ τ, D0 τ ≤ S + m * η + (if τ ∈ TT then bT τ else 0)) →
    (∀ τ, D1 τ ≤ 3 * D0 τ + S + η) →
    (∀ τ ∈ TT, bT τ ≤ 2 * b') →
    0 ≤ logT → logT ≤ CT * m * L → 0 ≤ CT → 0 ≤ b' →
    ev ≤ Cev * f * N ^ 2 * La → 0 ≤ Cev →

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b → 1 ≤ rd → La = Real.log (a * rd) →
    (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f → 1 ≤ k → k + m ≤ N → 0 ≤ S → 0 ≤ η →

    2 * (16 + CT + Cev) ≤ Ch →
    Cth + c5 + 2 * c6 + 1 + 2 * C4 + 2 * Ce * C8 ≤ Ch →
    2 * (C2 + C4) * (CT + C8) ≤ Ch →
      hP + ∑ j, hK j - mlam ≤ hu

end Formalism.DivisorInequality
