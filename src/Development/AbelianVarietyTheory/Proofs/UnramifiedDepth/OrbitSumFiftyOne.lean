import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DropLevelsBasic
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MulFlowValLe
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums

open scoped BigOperators
open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.OrbitPlan

theorem exists_good {S : ℕ} {G : Set ℕ} (h : Windows S G) {r : ℝ} (hr : 0 ≤ r) :
    ∃ y ∈ G, (y : ℝ) ≤ r ∧ r - y ≤ S := by
  have h1 := Nat.floor_le hr
  have h2 := Nat.lt_floor_add_one r
  by_cases hS : S ≤ ⌊r⌋₊ + 1
  · obtain ⟨y, hy, hy1, hy2⟩ := h.2 (⌊r⌋₊ + 1 - S)
    have a1 : y ≤ ⌊r⌋₊ := by omega
    have a2 : ⌊r⌋₊ + 1 ≤ y + S := by omega
    have b1 : (y : ℝ) ≤ ⌊r⌋₊ := by exact_mod_cast a1
    have b2 : (⌊r⌋₊ : ℝ) + 1 ≤ y + S := by exact_mod_cast a2
    exact ⟨y, hy, by linarith, by linarith⟩
  · have a2 : ⌊r⌋₊ + 1 ≤ S := by omega
    have b2 : (⌊r⌋₊ : ℝ) + 1 ≤ S := by exact_mod_cast a2
    exact ⟨0, h.1, by simpa using hr, by simp only [Nat.cast_zero]; linarith⟩

theorem logTerm_nonneg {l n : ℕ} (hl : 5 ≤ l) (hn : 1 ≤ n) :
    0 ≤ (n : ℝ) * (Real.logb l n + 1) := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have := Real.logb_nonneg h1 h2
  positivity

end GlobalTheory.OrbitPlan
