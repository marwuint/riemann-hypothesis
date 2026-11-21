import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqTwoMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormConjVacuumEqRankProductMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ErrorUnitExponentialEstimate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantTenth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantEleventh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantTwelfth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogMetricGeneratorEqMeanPeriod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyStandardLatticesEqBaseVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConstantExponentsFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumDatumNumbersEqHostOfCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIpAtNonneg

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.KernelHalf

open GlobalTheory.ColNorms GlobalTheory.ColNorms.NumMean

theorem exists_le_wtSum {α : Type} [Fintype α] (w f : α → ℝ) (h0 : ∀ a, 0 ≤ w a) (h1 : ∑ a, w a = 1) :
    ∃ a, w a ≠ 0 ∧ f a ≤ ∑ b, w b * f b := by
  by_contra hc
  push_neg at hc
  have h2 : ∑ a, w a * (∑ b, w b * f b) < ∑ a, w a * f a := by
    obtain ⟨a, ha⟩ : ∃ a, w a ≠ 0 := by
      by_contra h
      push_neg at h
      simp [h] at h1
    refine Finset.sum_lt_sum (fun b _ => ?_) ⟨a, Finset.mem_univ _, ?_⟩
    · by_cases hb : w b = 0
      · simp [hb]
      · exact mul_le_mul_of_nonneg_left (hc b hb).le (h0 b)
    · exact mul_lt_mul_of_pos_left (hc a ha) (lt_of_le_of_ne (h0 a) (Ne.symm ha))
  rw [← Finset.sum_mul, h1, one_mul] at h2
  exact lt_irrefl _ h2

theorem wt_affine {α Z : Type} [Fintype α] [Fintype Z] (w : α → ℝ) (hw : ∑ a, w a = 1) (p q : Z → ℝ) (o : α → Z → ℝ) (t : α → ℝ)
    (c₁ c₂ : ℝ) :
    ∑ a, w a * ((∑ z, (p z - q z * o a z)) + t a + c₁ + c₂) =
      (∑ z, (p z - q z * ∑ a, w a * o a z)) + (∑ a, w a * t a) + c₁ + c₂ := by
  have h1 : ∑ a, w a * ∑ z, (p z - q z * o a z) = ∑ z, (p z - q z * ∑ a, w a * o a z) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    have : ∑ a, w a * (p z - q z * o a z) = (∑ a, w a) * p z - ∑ a, q z * (w a * o a z) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, hw, one_mul]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul, h1]

theorem kernelBound_wt (N : NumDatum) (δ : Code N) (T : ℕ) (CK : ℝ) (j : ℕ) {α : Type} [Fintype α] (w : α → ℝ) (hw : ∑ a, w a = 1)
    (lo : α → RPl N.R → ℝ) (lt : α → ℝ) (h h' n n' : ℕ) :
    ∑ a, w a * kernelBound_sq N δ T CK j (lo a) (lt a) h h' n n' =
      kernelBound_sq N δ T CK j (fun z => ∑ a, w a * lo a z) (∑ a, w a * lt a) h h' n n' := by
  unfold kernelBound_sq
  exact wt_affine w hw _ _ lo lt _ _

theorem wt_mean {α Emb : Type} [Fintype α] [Fintype Emb] (wt : Emb → α → ℝ) (c d : ℝ) (h : ∀ a, (∑ v, wt v a) / c = 1 / d) (x : α → ℝ) :
    (∑ v, ∑ a, wt v a * x a) / c = (∑ a, x a) / d := by
  rw [Finset.sum_comm, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_mul, mul_div_right_comm, h a]
  ring

theorem sum_filter_eq {J : Type} [Fintype J] {m : ℕ} (eJ : J ≃ Fin m) (t : J → ℝ) {i : ℕ} (hi : i < m) :
    ∑ l ∈ Finset.univ.filter (fun l => (eJ l).1 = i), t l = t (eJ.symm ⟨i, hi⟩) := by
  have : Finset.univ.filter (fun l => (eJ l).1 = i) = {eJ.symm ⟨i, hi⟩} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      rw [Equiv.eq_symm_apply]
      exact Fin.ext h
    · rintro rfl
      simp
  rw [this, Finset.sum_singleton]

theorem sum_filter_ge {J : Type} [Fintype J] {m : ℕ} (hm : 2 ≤ m) (eJ : J ≃ Fin m) (t : J → ℝ) :
    ∑ l ∈ Finset.univ.filter (fun l => m - 2 ≤ (eJ l).1), t l =
      t (eJ.symm ⟨m - 2, by omega⟩) + t (eJ.symm ⟨m - 1, by omega⟩) := by
  classical
  have hne : eJ.symm ⟨m - 2, by omega⟩ ≠ eJ.symm ⟨m - 1, by omega⟩ := by
    intro h
    have := congrArg Fin.val (eJ.symm.injective h)
    simp only at this
    omega
  have : Finset.univ.filter (fun l => m - 2 ≤ (eJ l).1) = {eJ.symm ⟨m - 2, by omega⟩, eJ.symm ⟨m - 1, by omega⟩} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have h2 := (eJ l).2
      rcases (by omega : (eJ l).1 = m - 2 ∨ (eJ l).1 = m - 1) with h3 | h3
      · left
        rw [Equiv.eq_symm_apply]
        exact Fin.ext h3
      · right
        rw [Equiv.eq_symm_apply]
        exact Fin.ext h3
    · rintro (rfl | rfl) <;> simp <;> omega
  rw [this, Finset.sum_pair hne]

theorem factorBounds_of_weights {K : Type} [Field K] [NumberField K] [StarRing K] (Q : KerChain K) {α J : Type} [Fintype α] [Fintype J]
    {m : ℕ} (hm : 2 ≤ m) (hn : Q.n = m - 2) (eJ : J ≃ Fin m) (pu : α → InfinitePlace K) (wt : InfinitePlace K → α → ℝ)
    (h0 : ∀ v a, 0 ≤ wt v a) (h1 : ∀ v, ∑ a, wt v a = 1) (hup : ∀ v a, wt v a ≠ 0 → pu a = v) (lb : α → ℕ → ℝ)
    (hpos : ∀ i v φ, 0 ≤ (famIpAt (Q.F i) (Q.hF i) v φ φ).re)
    (hS : ∀ a i, i + 2 < m → StepBound_sq Q i (pu a) (lb a (i + 1)))
    (hC : ∀ a, CplBound_sq Q (pu a) (lb a (m - 1) + lb a m))
    (t : J → InfinitePlace K → ℝ) (ht : ∀ l v, t l v = ∑ a, wt v a * lb a ((eJ l).1 + 1)) :
    FactorBounds Q (fun l => (eJ l).1) t := by
  refine ⟨fun i hi v => ?_, fun v => ?_⟩
  · have hi' : i + 2 < m := by omega
    have hi1 : i < m := by omega
    rw [sum_filter_eq eJ (fun l => t l v) hi1, ht]
    obtain ⟨a, ha, hle⟩ := exists_le_wtSum (wt v) (fun a => lb a (i + 1)) (h0 v) (h1 v)
    have h2 := hS a i hi'
    rw [hup v a ha] at h2
    simp only [Equiv.apply_symm_apply]
    exact h2.mono hle (hpos i v)
  · rw [hn, sum_filter_ge hm eJ (fun l => t l v), ht, ht]
    obtain ⟨a, ha, hle⟩ := exists_le_wtSum (wt v) (fun a => lb a (m - 1) + lb a m) (h0 v) (h1 v)
    have h2 := hC a
    rw [hup v a ha] at h2
    simp only [Equiv.apply_symm_apply]
    have e1 : m - 2 + 1 = m - 1 := by omega
    have e2 : m - 1 + 1 = m := by omega
    rw [e1, e2, ← Finset.sum_add_distrib]
    simp only [mul_add] at hle
    intro φ
    refine (h2 φ).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hle) (hpos _ v φ))

theorem one_le_f (R : Ranks) : (1 : ℝ) ≤ R.f := by
  have : 1 ≤ R.f := by
    unfold Ranks.f Ranks.n
    have := And.intro (Nat.one_le_two_pow (n := R.e)) (show 0 < R.ord by positivity)
    omega
  exact_mod_cast this

theorem one_le_Nm (N : NumDatum) : (1 : ℝ) ≤ N.Nm := by
  have : 1 ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    have := N.R.m_add_three_le_k
    omega
  exact_mod_cast this

theorem L_le_La (N : NumDatum) : N.sc.L ≤ N.La := by
  have hb := two_le_b N.sc
  have hx := N.sc.one_lt_alt
  have hrd := one_le_rd N
  have h1 : N.sc.b ≤ N.sc.a := by
    unfold Scale.a
    exact le_mul_of_one_le_left (by linarith) hx.le
  have h2 : N.sc.a ≤ N.sc.a * N.rd := le_mul_of_one_le_right (by linarith) hrd
  calc N.sc.L = Real.log (Real.exp N.sc.L) := (Real.log_exp _).symm
    _ ≤ Real.log (N.sc.a * N.rd) := Real.log_le_log (Real.exp_pos _) (h1.trans h2)
    _ = N.La := rfl

end GlobalTheory.KernelHalf
