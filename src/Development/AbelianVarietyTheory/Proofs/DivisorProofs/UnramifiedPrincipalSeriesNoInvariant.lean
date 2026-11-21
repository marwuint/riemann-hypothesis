import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PrinTwo

namespace GlobalTheory.PrinTwo.NoFix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

theorem exists_unif : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  exact ⟨Units.mk0 x (by rintro rfl; exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)), hx⟩

end GlobalTheory.PrinTwo.NoFix

namespace GlobalTheory.PrinTwo.NoFix

end GlobalTheory.PrinTwo.NoFix

