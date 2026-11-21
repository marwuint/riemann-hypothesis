import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD cWt risingFactor DerivFormula)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt upIdele IsLatOf)
open GlobalTheory.ToricTransport (coordIn)
open scoped Classical

namespace GlobalTheory.LatConjOne

theorem exists_list_count {I : Type} [Fintype I] [DecidableEq I] (κ : I → ℕ) : ∃ u : List I, ∀ i, u.count i = κ i := by
  refine ⟨(∑ j, κ j • ({j} : Multiset I)).toList, fun i => ?_⟩
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum']
  simp [Multiset.count_singleton]

theorem exists_perm {K E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I]
    (ι : K →+* ℂ) (φ : I → E →+* ℂ) (g : ℂ ≃+* ℂ) (hφ : IsCMType φ) (hK : ∀ i, (φ i).comp (algebraMap K E) = ι)
    (hg : ∀ x, g (ι x) = ι x) (hr : ∃ x, starRingEnd ℂ (ι x) ≠ ι x) :
    ∃ π : I ≃ I, ∀ i, (g : ℂ →+* ℂ).comp (φ i) = φ (π i) := by
  have e : ∀ i x, φ i (algebraMap K E x) = ι x := fun i x => by rw [← RingHom.comp_apply, hK]
  have h1 : ∀ i, ∃ j, (g : ℂ →+* ℂ).comp (φ i) = φ j := by
    intro i
    obtain ⟨j, hj, -⟩ := hφ ((g : ℂ →+* ℂ).comp (φ i))
    rcases hj with hj | hj
    · exact ⟨j, hj⟩
    · exfalso
      obtain ⟨x, hx⟩ := hr
      have := congrArg (fun f : E →+* ℂ => f (algebraMap K E x)) hj
      simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq, Function.comp_apply, e] at this
      rw [RingEquiv.coe_toRingHom, hg] at this
      exact hx this.symm
  choose π hπ using h1
  have hinj : Function.Injective π := by
    intro i i' h
    have h2 : φ i = φ i' := by
      have h3 := (hπ i).trans ((congrArg φ h).trans (hπ i').symm)
      ext x
      have := congrArg (fun f : E →+* ℂ => f x) h3
      simpa using g.injective this
    obtain ⟨j, -, hj⟩ := hφ (φ i)
    rw [hj i (Or.inl rfl), hj i' (Or.inl h2)]
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.mp hinj), hπ⟩

end GlobalTheory.LatConjOne

namespace GlobalTheory.LatConjOne

theorem two_le_finrank_of_unramFin (E : Type) [Field E] [NumberField E] [IsCMField E] (h : UnramFin E) :
    2 ≤ Module.finrank ℚ (maximalRealSubfield E) := by
  by_contra hlt
  have hpos : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
  have h1 : Module.finrank ℚ (maximalRealSubfield E) = 1 := by omega
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hE : Module.finrank ℚ E = 2 := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, h1, h2]
  have hgt := NumberField.abs_discr_gt_two (K := E) (by omega)
  have hbt : (⊥ : Subalgebra ℚ (maximalRealSubfield E)) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  let f : (maximalRealSubfield E) ≃ₐ[ℚ] ℚ :=
    AlgEquiv.trans (Subalgebra.topEquiv (R := ℚ) (A := maximalRealSubfield E)).symm
      ((Subalgebra.equivOfEq _ _ hbt.symm).trans (Algebra.botEquiv ℚ (maximalRealSubfield E)))
  have hF : NumberField.discr (maximalRealSubfield E) = 1 := by
    rw [NumberField.discr_eq_discr_of_algEquiv _ f, Rat.numberField_discr]
  have key := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := maximalRealSubfield E) (𝒪 := 𝓞 (maximalRealSubfield E)) E (𝓞 E)
  have hU : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := h
  rw [hU, Ideal.absNorm_top, hF] at key
  simp at key
  rw [Int.abs_eq_natAbs, key] at hgt
  norm_num at hgt

end GlobalTheory.LatConjOne

namespace GlobalTheory.LatConjOne

theorem gamma_nat_add (k m : ℕ) (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + m) = ((k - 1).factorial : ℝ) * ∏ j ∈ Finset.range m, ((k : ℝ) + j) := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    have := Real.Gamma_nat_eq_factorial (k - 1)
    rwa [Nat.cast_sub hk, Nat.cast_one, sub_add_cancel] at this
  | succ m ih =>
    have h0 : (k : ℝ) + m ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      exact ne_of_gt (by linarith)
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one h0, ih]; ring

theorem cmPeriodConstant_eq_of_card_cmType (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (κ : I → ℕ) :
    (C0 E d k κ : ℂ) = (cWt E k : ℂ) * risingFactor k κ * (-1) ^ (∑ i, κ i) *
      ((2 * Real.pi / Real.sqrt d : ℝ) : ℂ) ^ (∑ i, κ i) := by
  rw [cmValueConst_eq]
  simp only [cWt, risingFactor, gamma_nat_add _ _ hk, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard,
    Finset.prod_pow_eq_pow_sum]
  have h1 : ((-1 : ℂ)) ^ (∑ i, κ i) * (-1) ^ (∑ i, κ i) = 1 := by rw [← mul_pow]; norm_num
  push_cast
  linear_combination (-(((|(discr (maximalRealSubfield E) : ℝ)| ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) *
    ((k - 1).factorial : ℂ) ^ Module.finrank ℚ (maximalRealSubfield E) * (∏ x, ∏ j ∈ Finset.range (κ x), ((k : ℂ) + j)) *
    (Real.pi : ℂ) ^ (∑ i, κ i) * ((Real.sqrt d : ℝ) : ℂ)⁻¹ ^ (∑ i, κ i) * 2 ^ (∑ i, κ i))) * h1

end GlobalTheory.LatConjOne

namespace GlobalTheory.LatConjOne

end GlobalTheory.LatConjOne
