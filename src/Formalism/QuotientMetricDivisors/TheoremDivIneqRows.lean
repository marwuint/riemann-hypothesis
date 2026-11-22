import Mathlib
import Formalism.QuotientMetricDivisors.StatementE
import Formalism.QuotientMetricDivisors.StatementK

open Finset

noncomputable section

namespace Formalism.DivisionValues

def phRows (lam : Multiset ℕ) : ℝ := (lam.map fun r : ℕ => Formalism.LatticeIndexTer.ph (r : ℝ)).sum

def logFactRows (lam : Multiset ℕ) : ℝ := (lam.map fun r : ℕ => Real.log (r.factorial : ℝ)).sum

def IsRowsOff (n w : ℕ) (S Bl sh : ℝ) (ν ap : Multiset ℕ) : Prop :=
  ∃ (c : Fin (n + 1) → ℕ) (c' r : Fin n → ℕ) (blk sm : Multiset ℕ),
    Formalism.LatticeIndexTer.Interlaced n (fun i => (c i : ℝ)) (fun i => (c' i : ℝ)) S ∧
    (∀ i, |(r i : ℝ) - ((w : ℝ) + (c' i : ℝ))| ≤ sh) ∧
    (blk.sum : ℝ) ≤ Bl ∧
    ν = (Finset.univ.val.map fun i => w + c i) + blk ∧
    ap = Finset.univ.val.map r + sm

def IsRowsTop (n aT w : ℕ) (S Bl sh : ℝ) (ν ap : Multiset ℕ) : Prop :=
  ∃ (c : Fin n → ℕ) (c' r : Fin (n + 1) → ℕ) (r0 : ℕ) (blk sm : Multiset ℕ),
    Formalism.LatticeIndexTer.Interlaced n (fun i => (c' i : ℝ)) (fun i => (c i : ℝ)) S ∧
    (∀ i, |(r i : ℝ) - ((w : ℝ) + (c' i : ℝ))| ≤ sh) ∧
    r0 ≤ w ∧
    (blk.sum : ℝ) ≤ Bl ∧
    ν = (aT + w) ::ₘ r0 ::ₘ ((Finset.univ.val.map fun i => w + c i) + blk) ∧
    ap = Finset.univ.val.map r + sm

def RowsFactorial : Prop :=
  ∀ (n w : ℕ) (S Bl sh A La fa : ℝ) (ν ap : Multiset ℕ),
    La = Real.log A → 1 ≤ La → (w : ℝ) + S ≤ A → Bl ≤ A → logFactRows ap ≤ fa →
    (IsRowsOff n w S Bl sh ν ap →
      phRows ν - fa ≤ ((w : ℝ) + 2 * S + (n : ℝ) * sh + Bl) * La) ∧
    (∀ aT : ℕ, (aT : ℝ) + (w : ℝ) ≤ A → IsRowsTop n aT w S Bl sh ν ap →
      phRows ν - fa ≤
        Formalism.LatticeIndexTer.ph (aT : ℝ) + ((2 * (w : ℝ) + S + (n : ℝ) * sh + Bl) * La + 1))

def RowsPeriod : Prop :=
  ∀ (n w : ℕ) (S Bl sh : ℝ) (ν ap : Multiset ℕ),
    (IsRowsOff n w S Bl sh ν ap →
      0 ≤ (ν.sum : ℝ) - ((n : ℝ) + 1) * (w : ℝ) ∧
      (ν.sum : ℝ) - ((n : ℝ) + 1) * (w : ℝ) ≤ ((n : ℝ) + 1) * S + Bl) ∧
    (∀ aT : ℕ, IsRowsTop n aT w S Bl sh ν ap →
      -(w : ℝ) ≤ (ν.sum : ℝ) - ((aT : ℝ) + ((n : ℝ) + 2) * (w : ℝ)) ∧
      (ν.sum : ℝ) - ((aT : ℝ) + ((n : ℝ) + 2) * (w : ℝ)) ≤ (n : ℝ) * S + Bl)

def RowsHook : Prop :=
  ∀ μ : YoungDiagram,
    logFactRows (μ.rowLens : Multiset ℕ) ≤ Real.log (Formalism.LatticeIndexTer.hookProd μ : ℝ)

def RowsStepE : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (n : ℕ) (aT : Pl → ℕ) (w : J → Pl → ℕ) (ν ap : J → Pl → Multiset ℕ) (fa : J → Pl → ℝ)
    (a rd La k N S Sc t η m b' cs C0 : ℝ),

    La = Real.log (a * rd) → 1 ≤ La → k = (n : ℝ) + 2 → k ≤ N → 0 ≤ b' → 0 ≤ cs →

    2 ≤ C0 → cs + 1 ≤ C0 → 2 * Sc ≤ C0 * S →

    (∀ j ρ, (w j ρ : ℝ) + Sc ≤ a * rd) → m * (t + 1) * η ≤ a * rd →
    (∀ j, ∀ ρ ∈ TT, (aT ρ : ℝ) + (w j ρ : ℝ) ≤ a * rd) →

    (∀ j ρ, logFactRows (ap j ρ) ≤ fa j ρ) →

    (∀ j, ∀ ρ, ρ ∉ TT →
      IsRowsOff (n + 1) (w j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →
    (∀ j, ∀ ρ ∈ TT,
      IsRowsTop n (aT ρ) (w j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →
    ∃ eE δ : J → Pl → ℝ,
      (∀ j ρ, phRows (ν j ρ) - fa j ρ ≤
        (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ : ℝ) else 0) + eE j ρ) ∧
      (∀ j ρ, ((ν j ρ).sum : ℝ) = (if ρ ∈ TT then (aT ρ : ℝ) else 0) + k * (w j ρ : ℝ) + δ j ρ) ∧
      (∀ j ρ, eE j ρ ≤ C0 * ((w j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η) * La) ∧
      (∀ j ρ, |δ j ρ| ≤
        C0 * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + (if ρ ∈ TT then k * b' else 0)))

end Formalism.DivisionValues
