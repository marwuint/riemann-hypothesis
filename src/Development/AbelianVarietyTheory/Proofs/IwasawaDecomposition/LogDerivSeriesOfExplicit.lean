import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumIndicatorLeZsumR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZeroSymmetry

open Finset ArithmeticFunction Filter Topology

noncomputable section

namespace GlobalTheory.MangoldtSeries

theorem sum_not_coprime_le (q N : ℕ) (hq : q ≠ 0) :
    ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Coprime q), Λ n ≤ Nat.log 2 N * Real.log q := by
  classical
  set S := (Icc 1 N).filter (fun n => ¬ n.Coprime q) with hS
  set L := Nat.log 2 N with hL
  have hT0 : ∀ p n : ℕ, 0 ≤ (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := by
    intro p n; split_ifs
    · exact Real.log_natCast_nonneg p
    · exact le_rfl
  have hpt : ∀ n ∈ S, Λ n ≤ ∑ p ∈ q.primeFactors,
      (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hnc⟩ := hn
    rw [ArithmeticFunction.vonMangoldt_apply]
    split_ifs with hpp
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
      have hmin : (p ^ k).minFac = p := by rw [Nat.pow_minFac hk.ne', hp.minFac_eq]
      have hpq : p ∣ q := by
        by_contra h
        exact hnc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 h))
      have hpmem : p ∈ q.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpq, hq⟩
      have hkL : k ∈ Icc 1 L := by
        rw [Finset.mem_Icc]
        refine ⟨hk, Nat.le_log_of_pow_le (by norm_num) ?_⟩
        exact (Nat.pow_le_pow_left hp.two_le k).trans hnN
      have hTp : (if p ^ k ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) = Real.log p :=
        if_pos (Finset.mem_image.2 ⟨k, hkL, rfl⟩)
      rw [hmin, ← hTp]
      exact Finset.single_le_sum (f := fun p' : ℕ => if p ^ k ∈ (Icc 1 L).image (p' ^ ·) then Real.log p' else 0)
        (fun p' _ => hT0 p' (p ^ k)) hpmem
    · exact Finset.sum_nonneg (fun p _ => hT0 p n)
  have hcard : ∀ p : ℕ, ((S ∩ (Icc 1 L).image (p ^ ·)).card : ℝ) ≤ L := by
    intro p
    have h1 := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := (Icc 1 L).image (p ^ ·)))
    have h2 := Finset.card_image_le (s := Icc 1 L) (f := (p ^ ·))
    have h3 : (Icc 1 L).card = L := by simp
    exact_mod_cast (h1.trans h2).trans h3.le
  calc ∑ n ∈ S, Λ n ≤ ∑ n ∈ S, ∑ p ∈ q.primeFactors,
        (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := Finset.sum_le_sum hpt
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ S,
        (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := Finset.sum_comm
    _ ≤ ∑ p ∈ q.primeFactors, (L : ℝ) * Real.log p := by
        apply Finset.sum_le_sum
        intro p _
        rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hcard p) (Real.log_natCast_nonneg p)
    _ = (L : ℝ) * Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
        rw [← Finset.mul_sum, Real.log_prod]
        intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ (L : ℝ) * Real.log q := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Real.log_le_log
        · apply Finset.prod_pos
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
        · rw [← Nat.cast_prod]
          exact Nat.cast_le.2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q))

theorem norm_sub_primitive_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) -
      ∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤
      Nat.log 2 N * Real.log q := by
  rw [← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not (Icc 1 N) (fun n => ¬ n.Coprime q)]
  rw [Finset.sum_eq_zero (s := (Icc 1 N).filter (fun n => ¬¬ n.Coprime q)) ?_, add_zero]
  · calc _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Coprime q),
          ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod q) -
            ((Λ n : ℝ) : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Coprime q), Λ n := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_filter] at hn
          have hχ0 : χ (n : ZMod q) = 0 := by
            apply MulChar.map_nonunit
            rw [ZMod.isUnit_iff_coprime]
            exact hn.2
          rw [hχ0, mul_zero, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          calc Λ n * ‖χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤ Λ n * 1 :=
                mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one _ _)
                  ArithmeticFunction.vonMangoldt_nonneg
            _ = Λ n := mul_one _
      _ ≤ _ := sum_not_coprime_le q N (NeZero.ne q)
  · intro n hn
    rw [Finset.mem_filter, not_not] at hn
    have h := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.2 hn.2)
    push_cast at h
    rw [h, sub_self]

end GlobalTheory.MangoldtSeries
