import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDegreeCountAlongFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePrimeValuationSumEqLogGapFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalRamifiedBoundAlongFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonnegConstDiscriminantTermLeBudgetFamilyA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimesLossLogSumAdmissible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleOffTypeFamilyBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePrimeSizesLeBudgetFamily

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory

theorem familySecondComplementInputs_of_tuSize_of_dGamSize : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → DGamSize Fm →
    Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm := by
  intro eps Fm h0 h1 hT hG
  obtain ⟨Cdeg, xd, -, hdeg⟩ := _root_.GlobalTheory.AdmissibleDegree.admissibleDegreeCount_along_family Fm h0 h1
  obtain ⟨Cg, xg, hCg, hsz⟩ := _root_.GlobalTheory.TypeSize.typePrimeSizeBound_of_eps_lt_one_div_fiftyTwo Fm h0 h1 hG Cdeg
  obtain ⟨CT, xT, -, hoT⟩ := _root_.GlobalTheory.LevelBudget.admissible_off_type_level_budget Fm h0 h1 hT
  obtain ⟨CG, xG, -, hoG⟩ := _root_.GlobalTheory.exists_nonneg_const_discriminant_term_le_budget_family Fm h0 h1 hT hG
  obtain ⟨Cd, xD, -, hoD⟩ := _root_.GlobalTheory.RamifiedOffD.offDiagonalRamified_bound_along_family Fm h0 h1
  obtain ⟨CI, xI, -, hoI⟩ := _root_.GlobalTheory.InertLossAdm.inertPrimes_loss_log_sum_admissible Fm h0 h1
  refine ⟨Cdeg, Cg, CT, CG, Cd, CI, max xd (max xg (max xT (max xG (max xD xI)))), hCg, ?_⟩
  intro x hx0 hx i
  have a1 : xd ≤ x := (le_max_left _ _).trans hx0
  have r1 := (le_max_right _ _).trans hx0
  have a2 : xg ≤ x := (le_max_left _ _).trans r1
  have r2 := (le_max_right _ _).trans r1
  have a3 : xT ≤ x := (le_max_left _ _).trans r2
  have r3 := (le_max_right _ _).trans r2
  have a4 : xG ≤ x := (le_max_left _ _).trans r3
  have r4 := (le_max_right _ _).trans r3
  have a5 : xD ≤ x := (le_max_left _ _).trans r4
  have a6 : xI ≤ x := (le_max_right _ _).trans r4
  exact ⟨fun u j h => (Fm.D x i).T_ne_g u j h.symm, _root_.GlobalTheory.TypeValNN.typePrime_valuationSum_eq_logGap_family Fm x hx i, hdeg x a1 hx i, hsz x a2 hx i,
    hoT x a3 hx i, hoG x a4 hx i, hoD x a5 hx i, hoI x a6 hx i⟩

end GlobalTheory
