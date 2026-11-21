import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Model

open Matrix
open scoped ComplexOrder

instance uniq1 : Unique {a : Fin 2 // (a : ℕ) < 1} where
  default := ⟨0, by simp⟩
  uniq := by rintro ⟨a, ha⟩; apply Subtype.ext; apply Fin.ext; simp only [Fin.val_zero]; omega

end GlobalTheory.CompanionTheory.Ar.PB.Model
