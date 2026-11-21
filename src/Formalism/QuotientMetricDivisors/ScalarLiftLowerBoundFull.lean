import Mathlib
import Formalism.QuotientMetricDivisors.StatementK
import Formalism.QuotientMetricDivisors.RatHermLcvTwist
import Formalism.QuotientMetricDivisors.EigenRatHermLcv
import Formalism.QuotientMetricDivisors.ClassSumDualLe
import Formalism.QuotientMetricDivisors.ClassSumDualGeF
import Formalism.QuotientMetricDivisors.UntwistedChoice
import Formalism.QuotientMetricDivisors.HeightBoundExactNorms
import Formalism.QuotientMetricDivisors.Complement2Normaliser
import Formalism.QuotientMetricDivisors.ScalarLiftLowerBoundRows

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.DivisionValues

def DivIneqRecord : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (muC mu0 Fo hu hP mlam logT : ℝ) (hK : J → ℝ) (aT : Pl → ℝ) (phν nν fa : J → Pl → ℝ)
    (x eps L b a rd La B0 Nc m f k N S tt η w'' b' lam0 C0 ce : ℝ)
    (Lpass Eb e6 eP logOm : ℝ) (eK pq : J → ℝ) (w eE δ : J → Pl → ℝ),
    muC ≤ mu0 + Lpass →
    mu0 ≤ ∑ j, ∑ ρ, pq j * w j ρ * logOm + 2 * Fo + Eb →
    hu = hP + ∑ j, hK j - mlam →
    (∀ j, hK j ≤ ∑ ρ, (phν j ρ - nν j ρ * logOm) + eK j) →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, aT t * logT) + eP →
    (∀ j ρ, phν j ρ - fa j ρ ≤ (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ) else 0) + eE j ρ) →
    (∀ j ρ, nν j ρ = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →
    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →
    B0 = f * m * b * x ^ eps → 0 ≤ Nc →
    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →
    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η →
    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →
    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →
    m * lam0 ≤ b → N ^ 2 ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →

    1 ≤ C0 → C0 ≤ ce →
    Lpass ≤ 1 + C0 * (m * lam0) →
    Eb ≤ ce * m * (x ^ eps * B0 + (Real.log x) ^ 2 * Nc) →
    (∀ j, eK j ≤ C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t) - aT t * logOm) - aT t * logT) +
        ((50 * C0 + 10) * ((TT.card : ℝ) * a * La) +
          60 * ce * (m * (x ^ eps * B0 + (Real.log x) ^ 2 * Nc)))

end Formalism.DivisionValues
