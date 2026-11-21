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

theorem IsProjPureDim.mem_projComponents_of_le {I P : Ideal (MvPolynomial ι k)} [hp : P.IsPrime]
    (h : IsProjPureDim I 0) (hP : P.IsHomogeneous (homogeneousSubmodule ι k)) (hIP : I ≤ P)
    {i : ι} (hi : (X i : MvPolynomial ι k) ∉ P) : P ∈ projComponents I := by
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_minimalPrimes_le hIP
  have hQc : Q ∈ projComponents I := ⟨hQ, i, fun h => hi (hle h)⟩
  have hd := h Q hQc
  have := hQ.1.1
  by_cases heq : Q = P
  · exact heq ▸ hQc
  exfalso
  have h1 := ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hle heq)
  obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_mvPolynomial_eq_nat hp.ne_top
  rw [hd, hδ] at h1
  obtain rfl : δ = 0 := by
    have : δ + 1 ≤ 0 + 1 := by exact_mod_cast h1
    omega
  have h2 := degree_idealHilbertPoly_lt hP hδ.le
  exact idealHilbertPoly_ne_zero_of_X_notMem hP hi (by simpa using h2)

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

omit [Finite ι] in

theorem exists_mem_projComponents_sup {I J Q : Ideal (MvPolynomial ι k)}
    (hQ : Q ∈ projComponents (I ⊔ J)) :
    ∃ P ∈ projComponents I, Q ∈ projComponents (P ⊔ J) := by
  have := hQ.1.1.1
  obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hQ.1.1.2)
  obtain ⟨i, hi⟩ := hQ.2
  exact ⟨P, ⟨hP, i, fun h => hi (hle h)⟩, ⟨⟨this, sup_le hle (le_sup_right.trans hQ.1.1.2)⟩,
    fun R hR hRQ => hQ.1.2 ⟨hR.1, (sup_le_sup_right hP.1.2 J).trans hR.2⟩ hRQ⟩, i, hi⟩

theorem projSetDegree_sup_le_sum (I J : Ideal (MvPolynomial ι k)) :
    projSetDegree (I ⊔ J) ≤ ∑ P ∈ (finite_projComponents I).toFinset, projSetDegree (P ⊔ J) := by
  classical
  refine le_trans (Finset.sum_le_sum_of_subset (t := (finite_projComponents I).toFinset.biUnion
    fun P => (finite_projComponents (P ⊔ J)).toFinset) ?_) ?_
  · intro Q hQ
    simpa using exists_mem_projComponents_sup (by simpa using hQ)
  · generalize (finite_projComponents I).toFinset = s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (Nat.le_add_right _ _).trans
        (Finset.sum_union_inter.le.trans (Nat.add_le_add_left ih _))

theorem projSetDegree_sup_le_of_forall_notMem {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) (h : ∀ P ∈ projComponents I, f ∉ P) :
    projSetDegree (I ⊔ Ideal.span {f}) ≤ d * projSetDegree I := by
  refine (projSetDegree_sup_le_sum I _).trans ?_
  rw [projSetDegree, Finset.mul_sum]
  refine Finset.sum_le_sum fun P hP => ?_
  rw [Set.Finite.mem_toFinset] at hP
  obtain ⟨i, hi⟩ := hP.2
  have := hP.1.1.1
  exact projSetDegree_sup_le_of_isPrime (isHomogeneous_of_mem_projComponents hI hP) hi hf (h P hP)

theorem IsProjPureDim.sup_span_singleton {I : Ideal (MvPolynomial ι k)} {e : ℕ}
    (he : IsProjPureDim I (e + 1)) (hI : I.IsHomogeneous (homogeneousSubmodule ι k))
    {f : MvPolynomial ι k} {d : ℕ} (hf : f.IsHomogeneous d)
    (h : ∀ P ∈ projComponents I, f ∉ P) : IsProjPureDim (I ⊔ Ideal.span {f}) e := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := exists_mem_projComponents_sup hQ
  have := hP.1.1.1
  obtain ⟨e', h1, h2⟩ := ringKrullDim_of_mem_projComponents_sup
    (isHomogeneous_of_mem_projComponents hI hP) (he P hP) hf (h P hP) hQP
  obtain rfl : e = e' := by omega
  exact h2

theorem IsProjPureDim.projComponents_sup_span_singleton {I : Ideal (MvPolynomial ι k)}
    (he : IsProjPureDim I 0) (hI : I.IsHomogeneous (homogeneousSubmodule ι k))
    {f : MvPolynomial ι k} {d : ℕ} (hf : f.IsHomogeneous d)
    (h : ∀ P ∈ projComponents I, f ∉ P) : projComponents (I ⊔ Ideal.span {f}) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun Q hQ => ?_
  obtain ⟨P, hP, hQP⟩ := exists_mem_projComponents_sup hQ
  have := hP.1.1.1
  obtain ⟨e', h1, -⟩ := ringKrullDim_of_mem_projComponents_sup
    (isHomogeneous_of_mem_projComponents hI hP) (he P hP) hf (h P hP) hQP
  omega

omit [Finite ι] in
theorem isHomogeneous_sup_span_range {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {σ : Type*} {f : σ → MvPolynomial ι k}
    {d : σ → ℕ} (hf : ∀ j, (f j).IsHomogeneous (d j)) (s : Set σ) :
    (I ⊔ Ideal.span (f '' s)).IsHomogeneous (homogeneousSubmodule ι k) :=
  hI.sup (Ideal.homogeneous_span _ _ (by rintro x ⟨j, -, rfl⟩; exact ⟨d j, hf j⟩))

def CutsProperly (I : Ideal (MvPolynomial ι k)) {s : ℕ} (f : Fin s → MvPolynomial ι k) : Prop :=
  ∀ j, ∀ P ∈ projComponents (I ⊔ Ideal.span (f '' Set.Iio j)), f j ∉ P

theorem CutsProperly.isProjPureDim_and_projSetDegree_le {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {s : ℕ} {f : Fin s → MvPolynomial ι k}
    {d : Fin s → ℕ} (hf : ∀ j, (f j).IsHomogeneous (d j)) (h : CutsProperly I f) :
    (∀ e, IsProjPureDim I (e + s) → IsProjPureDim (I ⊔ Ideal.span (Set.range f)) e) ∧
      projSetDegree (I ⊔ Ideal.span (Set.range f)) ≤ projSetDegree I * ∏ j, d j := by
  induction s with
  | zero => simp
  | succ s ih =>
    have e1 : ∀ j : Fin s, (fun j => f (Fin.castSucc j)) '' Set.Iio j =
        f '' Set.Iio (Fin.castSucc j) := by
      intro j
      rw [← Fin.image_castSucc_Iio, Set.image_image]
    have e2 : f '' Set.Iio (Fin.last s) = Set.range fun j => f (Fin.castSucc j) := by
      ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j.castPred (ne_of_lt hj), by simp⟩
      · rintro ⟨j, rfl⟩
        exact ⟨_, Fin.castSucc_lt_last j, rfl⟩
    have e3 : Set.range f = insert (f (Fin.last s)) (Set.range fun j => f (Fin.castSucc j)) := by
      ext x
      simp [Fin.exists_fin_succ', or_comm, eq_comm]
    obtain ⟨h1, h2⟩ := ih (f := fun j => f (Fin.castSucc j)) (d := fun j => d (Fin.castSucc j))
      (fun j => hf _) (fun j => by rw [e1]; exact h _)
    have hJ := isHomogeneous_sup_span_range hI hf (Set.Iio (Fin.last s))
    have hl := h (Fin.last s)
    rw [e2] at hJ hl
    rw [e3, Ideal.span_insert, sup_comm (Ideal.span {f _}), ← sup_assoc, Fin.prod_univ_castSucc]
    refine ⟨fun e he => (h1 (e + 1) (by rwa [add_assoc, add_comm 1 s])).sup_span_singleton hJ
      (hf _) hl, (projSetDegree_sup_le_of_forall_notMem hJ (hf _) hl).trans ?_⟩
    rw [← mul_assoc, mul_comm]
    exact Nat.mul_le_mul_right _ h2

end Degree

end GlobalTheory
