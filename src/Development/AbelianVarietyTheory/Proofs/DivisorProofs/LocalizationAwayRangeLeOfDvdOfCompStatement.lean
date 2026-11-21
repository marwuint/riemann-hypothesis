import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayRangeLeOfDvdOfComp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_away_range_le_of_dvd_of_comp : ∀ (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R), c ∣ c' → ∀ (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P), κ.comp (algebraMap R (Localization.Away c)) = g → κ'.comp (algebraMap R (Localization.Away c')) = g → κ.range ≤ κ'.range := by
  exact @GlobalTheory.away_range_le_of_dvd'
