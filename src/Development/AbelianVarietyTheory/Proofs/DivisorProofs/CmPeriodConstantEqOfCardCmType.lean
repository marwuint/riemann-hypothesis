import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.LatAlgebraic

theorem natAbs_discr_of_finrank_one (F : Type) [Field F] [NumberField F] (h : Module.finrank ℚ F = 1) :
    (discr F).natAbs = 1 := by
  have hb : (⊥ : Subalgebra ℚ F) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  let e : ℚ ≃ₐ[ℚ] F := (Algebra.botEquiv ℚ F).symm.trans ((Subalgebra.equivOfEq _ _ hb).trans Subalgebra.topEquiv)
  rw [← NumberField.discr_eq_discr_of_algEquiv (f := e), NumberField.discr_rat]
  rfl

theorem two_le_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] (h : UnramFin E) :
    2 ≤ Module.finrank ℚ (maximalRealSubfield E) := by
  by_contra hlt
  have h1 : Module.finrank ℚ (maximalRealSubfield E) = 1 := by
    have := Module.finrank_pos (R := ℚ) (M := maximalRealSubfield E)
    omega
  have hE := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (maximalRealSubfield E)
    (𝓞 (maximalRealSubfield E)) E (𝓞 E)
  have hU : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := h
  rw [hU, Ideal.absNorm_top, one_mul, natAbs_discr_of_finrank_one _ h1, one_pow] at hE
  have h2 : Module.finrank ℚ E = 2 := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, h1]
  have h3 := NumberField.abs_discr_gt_two (K := E) (by omega)
  have h4 : |(discr E : ℤ)| = 1 := by rw [Int.abs_eq_natAbs, hE]; rfl
  omega

theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (h : IsCMType φ) : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E) := by
  have hreal : ∀ i j, φ i ≠ ComplexEmbedding.conjugate (φ j) := by
    intro i j hij
    obtain ⟨k, -, hk⟩ := h (φ i)
    have e : i = j := (hk i (Or.inl rfl)).trans (hk j (Or.inr hij)).symm
    subst e
    have hr : ComplexEmbedding.IsReal (φ i) := ComplexEmbedding.isReal_iff.mpr hij.symm
    exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk (φ i)))
      (InfinitePlace.isReal_mk_iff.mpr hr)
  have hbij : Function.Bijective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))) := by
    refine ⟨?_, ?_⟩
    · rintro (i | i) (j | j) hij
      · simp only [Sum.elim_inl] at hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij)]
      · exact absurd hij (hreal i j)
      · exact absurd hij.symm (hreal j i)
      · simp only [Sum.elim_inr] at hij
        have hij' : φ i = φ j := by
          simpa using congrArg ComplexEmbedding.conjugate hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij')]
    · intro σ
      obtain ⟨k, hk, -⟩ := h σ
      rcases hk with hk | hk
      · exact ⟨Sum.inl k, hk.symm⟩
      · exact ⟨Sum.inr k, hk.symm⟩
  have h1 := Fintype.card_of_bijective hbij
  rw [Fintype.card_sum, NumberField.Embeddings.card E ℂ] at h1
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  omega

theorem gamma_nat_add (k n : ℕ) (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + n) = ((k - 1).factorial : ℝ) * ∏ j ∈ Finset.range n, ((k : ℝ) + j) := by
  induction n with
  | zero =>
    have : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hk]; ring
    simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    rw [this, Real.Gamma_nat_eq_factorial]
  | succ n ih =>
    have hpos : (k : ℝ) + n ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hpos, ih]
    ring

theorem exists_list_count {I : Type} [Fintype I] [DecidableEq I] (κ : I → ℕ) :
    ∃ u : List I, ∀ i, u.count i = κ i := by
  refine ⟨(∑ i, Multiset.replicate (κ i) i).toList, fun i => ?_⟩
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum', Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Multiset.count_replicate]
    simp [hj]
  · simp

theorem cmPeriodConstant_eq_of_card_cmType {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (d s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) :
    C0 E d (2 * s) κ = GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) *
      (∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) * (2 * Real.pi / Real.sqrt d) ^ (∑ i, κ i) := by
  have hk : 1 ≤ 2 * s := by omega
  rw [cmValueConst_eq, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt, Finset.prod_congr rfl (fun i _ => gamma_nat_add (2 * s) (κ i) hk),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
  ring

theorem risingFactor_eq {I : Type} [Fintype I] (k : ℕ) (κ : I → ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor k κ =
      (-1) ^ (∑ i, κ i) * (((∏ i, ∏ j ∈ Finset.range (κ i), ((k : ℝ) + j)) : ℝ) : ℂ) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  rfl

end GlobalTheory.LatAlgebraic
