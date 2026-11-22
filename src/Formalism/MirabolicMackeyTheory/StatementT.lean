import Mathlib
import Formalism.QuotientMetricDivisors.Statement

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def plc (w : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ w.asIdeal)

def ramw (w : HeightOneSpectrum (𝓞 K)) : ℤ := vw w ((plc w : ℕ) : K)

def ellw (w : HeightOneSpectrum (𝓞 K)) : ℝ := (plc w : ℝ) / Real.sqrt (ramw w : ℝ)

end Defs

def RamBasic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)),
    (plc w).Prime ∧ 1 ≤ ramw w ∧ plc (conjPl w) = plc w ∧ ramw (conjPl w) = ramw w ∧
      2 / ellw w ^ 2 = (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2)

def PlaceSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (X : ℕ → ℝ), (∀ p, 0 ≤ X p) →
      ∑ w ∈ S, lw w * ((ramw w : ℝ) * X (plc w)) ≤ ∑ p ∈ S.image plc, Real.log (p : ℝ) * X p

def DepthCases : Prop :=
  ∀ (e ec F : ℝ),
    (∀ a : ℝ, e ≤ F + a + 1 → ec ≤ F + a + 1 → e + ec - 2 * F ≤ 2 * a + 2) ∧
    (e = 0 → ec = 0 → 0 ≤ F → e + ec - 2 * F ≤ 0) ∧
    (∀ s T β : ℝ, e ≤ s + T + 1 → ec ≤ s + T + 1 → -(2 * β) ≤ F → F ≤ 0 →
      e + ec - 2 * F ≤ 2 * (s + T + 1) + 4 * β) ∧
    (∀ s T : ℝ, e ≤ s + T + 1 → ec ≤ s + T + 1 → F = 0 → e + ec - 2 * F ≤ 2 * s + 2 * T + 2) ∧
    (∀ T nn nnc g2 : ℝ, e ≤ 2 * T - nn → ec ≤ 2 * T - nnc → nn + nnc = -(2 * F) →
      e + ec - 2 * F + 2 * g2 ≤ 4 * T + 2 * g2)

def ShareNum : Prop :=
  ∀ (dK d0 d U δq ep y del : ℝ), 0 < U → 0 < δq → 0 ≤ dK → 0 ≤ d0 → 0 ≤ ep → ep ≤ y → y ≤ 1 / 8 →
    0 ≤ del → del ≤ 1 / 4 → (1 - ep) * dK ≤ U * d0 → (1 - y) * U ≤ δq → (1 - del) * d0 ≤ d →
      dK / δq ≤ 2 * d

def BudgetNum : Prop :=
  ∀ (dK δq D B : ℝ), 0 < δq → 0 < D → 0 ≤ B → dK / δq ≤ 3 * D →
    2 * (2 * (dK * B)) / (δq * D) ≤ 12 * B

def errGood (Y X2 A1 A2 kw T : ℝ) (th add : ℕ → ℝ) (p : ℕ) : ℝ :=
  if (p : ℝ) ≤ Y then
    2 * (A1 / (p : ℝ) + kw * th p + T * add p + (if X2 < (p : ℝ) then A2 / (p : ℝ) ^ 2 else 0)) + 2
  else 0

end Formalism.EigenvalueLevelCeiling
