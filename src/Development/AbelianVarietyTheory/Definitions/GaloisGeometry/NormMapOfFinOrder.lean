import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLocCharUnit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker

theorem norm_map_of_finOrder {K : Type} [Field K] (σ : K →+* ℂ) {ζ : Kˣ} (h : IsOfFinOrder ζ) : ‖σ (ζ : K)‖ = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 ?_
  rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, e, Units.val_one, map_one, norm_one]

end GlobalTheory.GO
