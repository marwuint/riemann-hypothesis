import Mathlib
import Formalism.QuotientMetricDivisors.TheoremDivIneqRows

open Finset

noncomputable section

namespace Formalism.DivisionValues

def RowsStepEShift : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (n : ℕ) (aT : Pl → ℕ) (w wr : J → Pl → ℕ) (ν ap : J → Pl → Multiset ℕ) (fa : J → Pl → ℝ)
    (a rd La k N S Sc t η m b' cs C1 C0 : ℝ),

    La = Real.log (a * rd) → 1 ≤ La → k = (n : ℝ) + 2 → k ≤ N → 0 ≤ b' → 0 ≤ cs → 0 ≤ S →

    2 ≤ C1 → cs + 1 ≤ C1 → 2 * Sc ≤ C1 * S → C1 + cs ≤ C0 →

    (∀ j ρ, wr j ρ ≤ w j ρ) → (∀ j ρ, (w j ρ : ℝ) - (wr j ρ : ℝ) ≤ cs * N) →

    (∀ j ρ, (w j ρ : ℝ) + Sc ≤ a * rd) → m * (t + 1) * η ≤ a * rd → 0 ≤ m * (t + 1) * η →
    (∀ j, ∀ ρ ∈ TT, (aT ρ : ℝ) + (w j ρ : ℝ) ≤ a * rd) →

    (∀ j ρ, logFactRows (ap j ρ) ≤ fa j ρ) →

    (∀ j, ∀ ρ, ρ ∉ TT →
      IsRowsOff (n + 1) (wr j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →
    (∀ j, ∀ ρ ∈ TT,
      IsRowsTop n (aT ρ) (wr j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →
    ∃ eE δ : J → Pl → ℝ,
      (∀ j ρ, phRows (ν j ρ) - fa j ρ ≤
        (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ : ℝ) else 0) + eE j ρ) ∧
      (∀ j ρ, ((ν j ρ).sum : ℝ) = (if ρ ∈ TT then (aT ρ : ℝ) else 0) + k * (w j ρ : ℝ) + δ j ρ) ∧
      (∀ j ρ, eE j ρ ≤ C0 * ((w j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η) * La) ∧
      (∀ j ρ, |δ j ρ| ≤
        C0 * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + (if ρ ∈ TT then k * b' else 0)))

def originRow (k t j w u i : ℝ) : ℝ :=
  (u + w) - ((k + (j - 1) * (t + 1)) + (k + j * (t + 1)) + 1 - 2 * i) / 2

def originBig (k m t j w v i : ℝ) : ℝ :=
  (v + w) - (((k - 1 + m) + t) + 1 - 2 * i) / 2 - ((k - 1 + j) - (m - j)) / 2

def RowsOriginOff : Prop :=
  ∀ (n j t w s wr : ℕ) (m Sc Bl sh : ℝ) (u : Fin (n + 2) → ℝ) (v : Fin (n + 1) → ℝ)
    (νr : Fin (n + 2) → ℕ) (ar : Fin (n + 1) → ℕ) (blk sm : Multiset ℕ),
    1 ≤ j → (s : ℝ) = (((n : ℝ) + 2) + (2 * (j : ℝ) - 1) * ((t : ℝ) + 1)) / 2 → wr + s = w →
    (∀ i, (νr i : ℝ) = originRow ((n : ℝ) + 2) t j w (u i) ((i : ℕ) + 1)) →
    (∀ i, (ar i : ℝ) = originBig ((n : ℝ) + 2) m t j w (v i) ((i : ℕ) + 1)) →
    (∀ i : Fin (n + 1), v i < u i.castSucc ∧ u i.succ < v i) →
    0 ≤ u (Fin.last (n + 1)) + (((n : ℝ) + 2) - 1) / 2 → u 0 - (((n : ℝ) + 2) - 1) / 2 ≤ Sc →
    ((j : ℝ) - 1) * (t : ℝ) ≤ sh → (blk.sum : ℝ) ≤ Bl →
      IsRowsOff (n + 1) wr Sc Bl sh (Finset.univ.val.map νr + blk) (Finset.univ.val.map ar + sm)

def RowsOriginTop : Prop :=
  ∀ (n j t w s wr aT bT : ℕ) (m Sc Bl sh : ℝ) (u : Fin (n + 2) → ℝ) (v : Fin (n + 1) → ℝ)
    (νr : Fin (n + 2) → ℕ) (ar : Fin (n + 1) → ℕ) (blk sm : Multiset ℕ),
    1 ≤ j → (s : ℝ) = (((n : ℝ) + 2) + (2 * (j : ℝ) - 1) * ((t : ℝ) + 1)) / 2 → wr + s = w →
    (∀ i, (νr i : ℝ) = originRow ((n : ℝ) + 2) t j w (u i) ((i : ℕ) + 1)) →
    (∀ i, (ar i : ℝ) = originBig ((n : ℝ) + 2) m t j w (v i) ((i : ℕ) + 1)) →
    (∀ i : Fin (n + 1), v i < u i.castSucc ∧ u i.succ < v i) →
    u 0 = (aT : ℝ) + (((n : ℝ) + 2) - 1) / 2 → u (Fin.last (n + 1)) = -(bT : ℝ) - (((n : ℝ) + 2) - 1) / 2 →
    0 ≤ v (Fin.last n) + (((n : ℝ) + 2) - 2) / 2 → v 0 - (((n : ℝ) + 2) - 2) / 2 ≤ Sc →
    ((j : ℝ) - 1) * (t : ℝ) ≤ sh → (blk.sum : ℝ) ≤ Bl →
      IsRowsTop n aT wr Sc Bl sh (Finset.univ.val.map νr + blk) (Finset.univ.val.map ar + sm)

def RowsStepEOrigin : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (n t : ℕ) (jj s : J → ℕ) (aT bT : Pl → ℕ) (w : J → Pl → ℕ)
    (u : Pl → Fin (n + 2) → ℝ) (v : Pl → Fin (n + 1) → ℝ)
    (νr : J → Pl → Fin (n + 2) → ℕ) (ar : J → Pl → Fin (n + 1) → ℕ) (blk sm : J → Pl → Multiset ℕ)
    (ν ap : J → Pl → Multiset ℕ) (fa : J → Pl → ℝ)
    (a rd La k N S Sc η m b' C1 C0 : ℝ),

    La = Real.log (a * rd) → 1 ≤ La → k = (n : ℝ) + 2 → 0 ≤ m → k + m * ((t : ℝ) + 1) ≤ N →
    0 ≤ b' → 0 ≤ S →

    2 ≤ C1 → 2 * Sc ≤ C1 * S → C1 + 1 ≤ C0 →

    (∀ j, 1 ≤ jj j) → (∀ j, (jj j : ℝ) ≤ m) →
    (∀ j, (s j : ℝ) = (k + (2 * (jj j : ℝ) - 1) * ((t : ℝ) + 1)) / 2) → (∀ j ρ, s j ≤ w j ρ) →

    (∀ j ρ, (w j ρ : ℝ) + Sc ≤ a * rd) → m * ((t : ℝ) + 1) * η ≤ a * rd → 0 ≤ m * ((t : ℝ) + 1) * η →
    (∀ j, ∀ ρ ∈ TT, (aT ρ : ℝ) + (w j ρ : ℝ) ≤ a * rd) →

    (∀ j ρ, logFactRows (ap j ρ) ≤ fa j ρ) →

    (∀ j ρ, ν j ρ = Finset.univ.val.map (νr j ρ) + blk j ρ) →
    (∀ j ρ, ap j ρ = Finset.univ.val.map (ar j ρ) + sm j ρ) →
    (∀ j ρ i, (νr j ρ i : ℝ) = originRow k t (jj j) (w j ρ) (u ρ i) ((i : ℕ) + 1)) →
    (∀ j ρ i, (ar j ρ i : ℝ) = originBig k m t (jj j) (w j ρ) (v ρ i) ((i : ℕ) + 1)) →
    (∀ j ρ, ((blk j ρ).sum : ℝ) ≤ m * ((t : ℝ) + 1) * η) →

    (∀ ρ, ∀ i : Fin (n + 1), v ρ i < u ρ i.castSucc ∧ u ρ i.succ < v ρ i) →
    (∀ ρ, ρ ∉ TT → 0 ≤ u ρ (Fin.last (n + 1)) + (k - 1) / 2 ∧ u ρ 0 - (k - 1) / 2 ≤ Sc) →
    (∀ ρ ∈ TT, u ρ 0 = (aT ρ : ℝ) + (k - 1) / 2 ∧ u ρ (Fin.last (n + 1)) = -(bT ρ : ℝ) - (k - 1) / 2 ∧
      0 ≤ v ρ (Fin.last n) + (k - 2) / 2 ∧ v ρ 0 - (k - 2) / 2 ≤ Sc) →
    ∃ eE δ : J → Pl → ℝ,
      (∀ j ρ, phRows (ν j ρ) - fa j ρ ≤
        (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ : ℝ) else 0) + eE j ρ) ∧
      (∀ j ρ, ((ν j ρ).sum : ℝ) = (if ρ ∈ TT then (aT ρ : ℝ) else 0) + k * (w j ρ : ℝ) + δ j ρ) ∧
      (∀ j ρ, eE j ρ ≤ C0 * ((w j ρ : ℝ) + S + N ^ 2 + m * ((t : ℝ) + 1) * η) * La) ∧
      (∀ j ρ, |δ j ρ| ≤
        C0 * ((w j ρ : ℝ) + k * (N + S) + m * ((t : ℝ) + 1) * η + (if ρ ∈ TT then k * b' else 0)))

end Formalism.DivisionValues
