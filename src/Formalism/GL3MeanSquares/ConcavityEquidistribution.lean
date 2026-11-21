import Mathlib
import Formalism.LogVandermondeBounds.MultinomialPowerBound

namespace Formalism.HermitianLattices.TraceIntegrality

open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)

noncomputable def mean {σ : Type} [Fintype σ] (F : σ → ℝ) : ℝ := (∑ s, F s) / (Fintype.card σ : ℝ)

noncomputable def weylDim {n : ℕ} (lam : Fin n → ℤ) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ univ.filter (fun j => i < j),
    (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))

def Wnum {n : ℕ} (lam : Fin (n + 1) → ℤ) : ℤ := lam 0 - lam (Fin.last n) + n + 1

def degZ {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) : ℤ := ∑ i, lam i - ∑ i, nu i

noncomputable def MeanSquareTwistBound {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) (logT : ℝ) : ℝ :=
  -(degZ lam nu : ℝ) * logT
    + 2 * (n : ℝ) * Real.log (Wnum lam : ℝ) * (∑ i, ((min (len lam i) (B0 lam nu) : ℤ) : ℝ))
    + Real.log (weylDim lam)

def wt {k : ℕ} (lam : Fin k → ℤ) : ℤ := ∑ i, lam i

def plus {κ : ℕ} (lam : Fin (κ + 1) → ℤ) : Fin (κ + 1) → ℤ := fun i => lam i - lam (Fin.last κ)

noncomputable def MeanSquareWeightBound {κ : ℕ} (lam : Fin (κ + 1) → ℤ) : ℝ :=
  (wt (plus lam) : ℝ) * Real.log ((κ : ℝ) + 1)
    + ((κ : ℝ) + 1) ^ 2 * Real.log ((plus lam 0 : ℝ) + (κ : ℝ) + 1)

structure Numbers (C₀ a b' L v logT logg eta S : ℝ) (k m t N : ℕ) : Prop where
  one_le_L : 1 ≤ L
  one_le_v : 1 ≤ v
  log_av : Real.log (a * v) ≤ L
  one_le_b' : 1 ≤ b'
  b'_le_a : b' ≤ a
  logT_nonneg : 0 ≤ logT
  logT_le : logT ≤ C₀ * m * L
  logg_nonneg : 0 ≤ logg
  logg_le : logg ≤ C₀ * L
  one_le_k : 1 ≤ k
  one_le_m : 1 ≤ m
  N_eq : N = k + m * (t + 1)
  eta_nonneg : 0 ≤ eta
  S_nonneg : 0 ≤ S
  small : S + eta + (m : ℝ) * t ≤ b'
  sq : (N : ℝ) ^ 2 * (L + logT) ≤ N * b'
  lin : (N : ℝ) * L + logT ≤ b'
  pow : (1 + 2 * C₀) * (m : ℝ) ^ 3 * N ≤ b'

def ZetaBoundApplication : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (TT : Finset ι) (n : ℕ)
    (lam : ι → Fin (n + 1) → ℤ) (sg : ι → Fin n → ℤ) (A bt : ι → ℝ)
    (b' L logT eta S mt logP : ℝ),
    1 ≤ L → 0 ≤ logT → 0 ≤ b' → 0 ≤ eta → 0 ≤ S → 0 ≤ mt →
    (∀ ρ, Interlace (lam ρ) (sg ρ)) → (∀ ρ, Real.log (Wnum (lam ρ) : ℝ) ≤ C₀ * L) →
    (∀ ρ ∈ TT, bt ρ ≤ 2 * b') →
    (∀ ρ ∈ TT, (B0 (lam ρ) (sg ρ) : ℝ) ≤ bt ρ + eta + S) →
    (∀ ρ, ρ ∉ TT → (B0 (lam ρ) (sg ρ) : ℝ) ≤ eta + S) →
    (∀ ρ, ∃ X : Finset (Fin n), X.card ≤ 3 ∧ ((∑ i ∈ Xᶜ, len (lam ρ) i : ℤ) : ℝ) ≤ eta + S) →
    (∀ ρ ∈ TT, A ρ - bt ρ - C₀ * (S + eta + mt) ≤ (degZ (lam ρ) (sg ρ) : ℝ)) →
    (∀ ρ, ρ ∉ TT → -(S + eta) - C₀ * mt ≤ (degZ (lam ρ) (sg ρ) : ℝ)) →
    logP ≤ ∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT →
    logP ≤ -(∑ ρ ∈ TT, A ρ) * logT + C * TT.card * b' * (logT + ((n : ℝ) + 1) * L)
        + C * Fintype.card ι * (eta + 3 * S + mt) * (logT + ((n : ℝ) + 1) * L)
        + C * Fintype.card ι * ((n : ℝ) + 1) ^ 2 * L

def LastColumnBound : Prop :=
  ∀ (κ : ℕ) (lam : Fin (κ + 1 + 1) → ℤ) (A bt S : ℤ), 0 ≤ bt → 0 ≤ S →
    lam 0 = A → lam (Fin.last (κ + 1)) = -bt →
    (∀ i, i ≠ 0 → i ≠ Fin.last (κ + 1) → 0 ≤ lam i ∧ lam i ≤ S) →
    wt lam ≤ A + (κ + 2) * S ∧ wt (plus lam) ≤ A + (κ + 2) * (bt + S)

def PropZ_ii : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (ι X : Type) [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X]
    (TT : Finset ι) (κ m t N : ℕ) (lam : ι → Fin (κ + 1) → ℤ) (A bt : ι → ℝ)
    (a b' L v logT logg eta S muM : ℝ) (muV : X → ℝ) (muDelta muNabla muMaxNabla : ι → ℝ),
    Numbers C₀ a b' L v logT logg eta S (κ + 1) m t N →
    (∀ ρ, Antitone (lam ρ)) →
    (∀ τ ∈ TT, a ≤ A τ ∧ A τ ≤ 2 * a ∧ b' ≤ bt τ ∧ bt τ ≤ 2 * b') →
    (∀ τ ∈ TT, (wt (lam τ) : ℝ) ≤ A τ + ((κ : ℝ) + 1) * S) →
    (∀ τ ∈ TT, (wt (plus (lam τ)) : ℝ) ≤ A τ + ((κ : ℝ) + 1) * (bt τ + S)) →
    (∀ ρ, ρ ∉ TT → (wt (plus (lam ρ)) : ℝ) ≤ ((κ : ℝ) + 1 + 3) * S) →
    (∀ ρ, ρ ∉ TT → (wt (lam ρ) : ℝ) ≤ C₀ * ((κ : ℝ) + 1) * S) →
    muM = mean muV →
    (∀ c, muV c = -(∑ ρ, (wt (lam ρ) : ℝ) / ((κ : ℝ) + 1) * logT) + ∑ ρ, muDelta ρ) →
    (∀ ρ, muDelta ρ = -muNabla ρ) → (∀ ρ, muNabla ρ ≤ muMaxNabla ρ) →
    (∀ ρ, muMaxNabla ρ ≤ MeanSquareWeightBound (lam ρ)) →
    -(∑ τ ∈ TT, A τ / ((κ : ℝ) + 1) * logT) - C * TT.card * a * Real.log ((κ : ℝ) + 1)
        - C * Fintype.card ι * ((κ : ℝ) + 1) * (b' + S) * Real.log ((κ : ℝ) + 1)
        - C * Fintype.card ι * S * logT - C * Fintype.card ι * ((κ : ℝ) + 1) ^ 2 * L ≤ muM

def PropZ_iii : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (ι X : Type) [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X]
    (TT : Finset ι) (κ m t N : ℕ) (lam : ι → Fin (κ + 1) → ℤ) (A bt : ι → ℝ)
    (a b' L v logT logg eta S muMaxM : ℝ) (muMaxV : X → ℝ),
    Numbers C₀ a b' L v logT logg eta S (κ + 1) m t N →
    (∀ ρ, Antitone (lam ρ)) →
    (∀ τ ∈ TT, a ≤ A τ ∧ A τ ≤ 2 * a ∧ b' ≤ bt τ ∧ bt τ ≤ 2 * b') →
    (∀ τ ∈ TT, (wt (plus (lam τ)) : ℝ) ≤ A τ + ((κ : ℝ) + 1) * (bt τ + S)) →
    (∀ τ ∈ TT, |(lam τ (Fin.last κ) : ℝ)| ≤ bt τ) →
    (∀ ρ, ρ ∉ TT → (wt (plus (lam ρ)) : ℝ) ≤ ((κ : ℝ) + 1 + 3) * S) →
    (∀ ρ, ρ ∉ TT → |(lam ρ (Fin.last κ) : ℝ)| ≤ C₀ * S) →
    (∃ c, muMaxM ≤ muMaxV c) →
    (∀ c, muMaxV c ≤ ∑ ρ, ((wt (plus (lam ρ)) : ℝ) * (C₀ * Real.log (((κ : ℝ) + 1) * v))
        + ((κ : ℝ) + 1) ^ 2 * Real.log ((plus (lam ρ) 0 : ℝ) + (κ : ℝ) + 1)
        + |(lam ρ (Fin.last κ) : ℝ)| * logT)) →
    muMaxM ≤ C * TT.card * a * Real.log (((κ : ℝ) + 1) * v)
        + C * Fintype.card ι * (b' + S) * (((κ : ℝ) + 1) * Real.log (((κ : ℝ) + 1) * v) + logT)
        + C * Fintype.card ι * ((κ : ℝ) + 1) ^ 2 * L

end Formalism.HermitianLattices.TraceIntegrality
