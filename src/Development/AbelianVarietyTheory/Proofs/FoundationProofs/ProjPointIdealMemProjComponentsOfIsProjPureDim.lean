import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MonomialCountAndBinomialEstimates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup

open Polynomial Filter Module

namespace GlobalTheory

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ringKrullDim_quotient_add_one_le_of_lt {A : Type*} [CommRing A] {Q P : Ideal A}
    [Q.IsPrime] (h : Q < P) : ringKrullDim (A ⧸ P) + 1 ≤ ringKrullDim (A ⧸ Q) := by
  obtain ⟨g, hg, hgQ⟩ := SetLike.exists_of_lt h
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor h.le)
    (Ideal.Quotient.factor_surjective _) (r := Ideal.Quotient.mk Q g)
    (mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])) (by
      rwa [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem])

open MvPolynomial DirectSum

variable {ι k : Type*} [Field k]

section Points

noncomputable def projPointIdeal (y : Projectivization k (ι → k)) : Ideal (MvPolynomial ι k) :=
  ((RingHom.ker (MvPolynomial.eval y.rep)).homogeneousCore (homogeneousSubmodule ι k)).toIdeal

instance isPrime_projPointIdeal (y : Projectivization k (ι → k)) : (projPointIdeal y).IsPrime :=
  (RingHom.ker_isPrime _).homogeneousCore

variable [Finite ι]

end Points

section Degree

variable [Finite ι]

omit [Finite ι] in
theorem isHomogeneous_of_mem_projComponents {I P : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) (hP : P ∈ projComponents I) :
    P.IsHomogeneous (homogeneousSubmodule ι k) :=
  isHomogeneous_of_mem_minimalPrimes _ hI hP.1

theorem hilbertDegree_pos {P : Ideal (MvPolynomial ι k)} [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule ι k)) {i : ι}
    (h : (X i : MvPolynomial ι k) ∉ P) : 0 < hilbertDegree P :=
  Nat.pos_of_ne_zero fun h0 =>
    idealHilbertPoly_ne_zero_of_X_notMem hP h ((hilbertDegree_eq_zero_iff hP).1 h0)

theorem exists_ringKrullDim_quotient_eq_succ {P : Ideal (MvPolynomial ι k)} [hp : P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule ι k)) {i : ι}
    (h : (X i : MvPolynomial ι k) ∉ P) :
    ∃ e : ℕ, ringKrullDim (MvPolynomial ι k ⧸ P) = (e + 1 : ℕ) := by
  obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_mvPolynomial_eq_nat hp.ne_top
  cases δ with
  | zero =>
    exact absurd (by simpa using degree_idealHilbertPoly_lt hP hδ.le)
      (idealHilbertPoly_ne_zero_of_X_notMem hP h)
  | succ e => exact ⟨e, hδ⟩

theorem ringKrullDim_of_mem_projComponents_sup {P Q : Ideal (MvPolynomial ι k)} [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule ι k)) {e : ℕ}
    (he : ringKrullDim (MvPolynomial ι k ⧸ P) = (e + 1 : ℕ)) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hfP : f ∉ P) (hQ : Q ∈ projComponents (P ⊔ Ideal.span {f})) :
    ∃ e' : ℕ, e = e' + 1 ∧ ringKrullDim (MvPolynomial ι k ⧸ Q) = (e' + 1 : ℕ) := by
  obtain ⟨i, hi⟩ := hQ.2
  have := hQ.1.1.1
  obtain ⟨e', he'⟩ := exists_ringKrullDim_quotient_eq_succ
    (isHomogeneous_of_mem_projComponents (isHomogeneous_sup_span_singleton hP hf) hQ) hi
  have h1 := ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup k hfP hQ.1
  rw [he, he'] at h1
  have : e' + 1 + 1 = e + 1 := by exact_mod_cast h1
  exact ⟨e', by omega, he'⟩

theorem projSetDegree_sup_le_of_isPrime {P : Ideal (MvPolynomial ι k)} [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule ι k)) {i : ι}
    (hi : (X i : MvPolynomial ι k) ∉ P) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hfP : f ∉ P) :
    projSetDegree (P ⊔ Ideal.span {f}) ≤ d * hilbertDegree P := by
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ hP hi
  have hJ := isHomogeneous_sup_span_singleton hP hf
  cases e with
  | zero =>
    rw [projSetDegree, Finset.sum_eq_zero]
    · exact Nat.zero_le _
    intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    obtain ⟨e', h, -⟩ := ringKrullDim_of_mem_projComponents_sup hP he hf hfP hQ
    omega
  | succ e =>
    have hdeg := degree_idealHilbertPoly_eq_of_isPrime hP he
    obtain ⟨h1, h2⟩ := coeff_sub_comp_X_sub_C (idealHilbertPoly P) (d : ℚ) e hdeg.le
    rw [← idealHilbertPoly_sup_of_isPrime hP hf hfP] at h1 h2
    have h3 : (idealHilbertPoly (P ⊔ Ideal.span {f})).degree ≤ e :=
      (degree_le_iff_coeff_zero _ _).2 fun m hm =>
        (degree_lt_iff_coeff_zero _ _).1 h1 m (by exact_mod_cast hm)
    have h4 := sum_coeff_idealHilbertPoly_minimalPrimes_le hJ h3
    have h5 : (projSetDegree (P ⊔ Ideal.span {f}) : ℚ) ≤ e.factorial *
        ∑ Q ∈ (P ⊔ Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing.toFinset,
          (idealHilbertPoly Q).coeff e := by
      rw [projSetDegree, Nat.cast_sum, Finset.mul_sum]
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun Q hQ => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg
          (s := (finite_projComponents (P ⊔ Ideal.span {f})).toFinset) (fun Q hQ => ?_) ?_)
      · rw [Set.Finite.mem_toFinset] at hQ
        obtain ⟨e', h, hQe⟩ := ringKrullDim_of_mem_projComponents_sup hP he hf hfP hQ
        obtain rfl : e = e' := by omega
        have := hQ.1.1.1
        have hQh := isHomogeneous_of_mem_projComponents hJ hQ
        exact cast_hilbertDegree_of_degree_eq hQh (degree_idealHilbertPoly_eq_of_isPrime hQh hQe)
      · rw [Set.Finite.mem_toFinset] at hQ ⊢
        exact hQ.1
      · intro Q hQ _
        rw [Set.Finite.mem_toFinset] at hQ
        have hQh := isHomogeneous_of_mem_minimalPrimes _ hJ hQ
        exact mul_nonneg (by positivity) (coeff_nonneg_of_eventually_eval_nat
          ((degree_idealHilbertPoly_anti hJ hQh hQ.1.2).trans h3)
          (eventually_idealHilbertPoly_nonneg hQh))
    have h6 := h5.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
    rw [h2] at h6
    have h7 : (projSetDegree (P ⊔ Ideal.span {f}) : ℚ) ≤ d * hilbertDegree P := by
      rw [cast_hilbertDegree_of_degree_eq hP hdeg, Nat.factorial_succ]
      push_cast
      linarith
    exact_mod_cast h7

end Degree

end GlobalTheory
