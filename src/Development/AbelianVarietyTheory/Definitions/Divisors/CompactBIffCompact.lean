import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

noncomputable section

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime]

def Datum.CompactB (D : Datum p) : Prop := 2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)

theorem Datum.compactB_iff_compact (D : Datum p) : D.CompactB ↔ D.Compact := Iff.rfl

end GlobalTheory.UPel.HT
