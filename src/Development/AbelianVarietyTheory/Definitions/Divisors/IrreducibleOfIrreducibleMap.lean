import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.AevalEqZeroOfHomogeneousComponent

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.ChowHt

attribute [local instance] MvPolynomial.gradedAlgebra

structure IsChowFormInt {k : Type} [Field k] {N : ℕ} (I : Ideal (MvPolynomial (Fin N) k))
    (e dl : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin N) k) : Prop where

  homog : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => dl) f

  irred : Irreducible f

  zero_iff : ∀ u : Fin (e + 1) × Fin N → AlgebraicClosure k, MvPolynomial.aeval u f = 0 ↔
    ∃ y : Fin N → AlgebraicClosure k, y ≠ 0 ∧ (∀ g ∈ I, MvPolynomial.aeval y g = 0) ∧
      ∀ i, ∑ j, u (i, j) * y j = 0

def IsChowFormCycle {k : Type} [Field k] {N : ℕ} (Z : Ideal (MvPolynomial (Fin N) k) →₀ ℕ)
    (e dl : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin N) k) : Prop :=
  ∃ c : k, c ≠ 0 ∧ ∃ (d : Ideal (MvPolynomial (Fin N) k) → ℕ)
    (g : Ideal (MvPolynomial (Fin N) k) → MvPolynomial (Fin (e + 1) × Fin N) k),
    (∀ P ∈ Z.support, P.IsPrime ∧ P.IsHomogeneous (homogeneousSubmodule (Fin N) k) ∧
      IsChowFormInt P e (d P) (g P)) ∧
    dl = Z.sum (fun P m => m * d P) ∧ f = C c * Z.prod (fun P m => g P ^ m)

variable {k : Type} [Field k] {N : ℕ}

theorem isMultiHomogeneous_iff_block {B : ℕ} {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) k} :
    ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f ↔ GlobalTheory.Chow.IsBlockHomogeneous f a :=
  GlobalTheory.Chow.isBlockHomogeneous_iff.symm

theorem irreducible_of_irreducible_map {K σ : Type} [Field K] [Algebra k K] {f : MvPolynomial σ k}
    (h : Irreducible (MvPolynomial.map (algebraMap k K) f)) : Irreducible f := by
  have key : ∀ a : MvPolynomial σ k, IsUnit (MvPolynomial.map (algebraMap k K) a) → IsUnit a := by
    intro a ha
    obtain ⟨c, hc, hca⟩ := isUnit_iff_eq_C_of_isReduced.1 ha
    have h0 : algebraMap k K (coeff 0 a) = c := by
      have := congrArg (coeff 0) hca
      rwa [coeff_map, coeff_zero_C] at this
    have ha' : a = C (coeff 0 a) := by
      apply map_injective (algebraMap k K) (algebraMap k K).injective
      rw [map_C, h0, hca]
    rw [ha']
    refine (IsUnit.mk0 _ fun h => hc.ne_zero ?_).map C
    rw [← h0, h, map_zero]
  refine ⟨fun hu => h.not_isUnit (hu.map _), fun a b hab => ?_⟩
  rw [hab, map_mul] at h
  exact (h.isUnit_or_isUnit rfl).imp (key a) (key b)

theorem IsChowForm.isChowFormInt {I : Ideal (MvPolynomial (Fin N) k)} {e dl : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin N) k} (h : IsChowForm I e dl f) :
    IsChowFormInt I e dl f :=
  ⟨h.homog, irreducible_of_irreducible_map h.irred, h.zero_iff⟩

namespace IsChowFormInt

variable {I : Ideal (MvPolynomial (Fin N) k)} {e dl dl' : ℕ}
  {f f' : MvPolynomial (Fin (e + 1) × Fin N) k}

theorem ne_zero (h : IsChowFormInt I e dl f) : f ≠ 0 := h.irred.ne_zero

theorem isChowForm (h : IsChowFormInt I e dl f)
    (hf : Irreducible (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f)) :
    IsChowForm I e dl f := ⟨h.homog, hf, h.zero_iff⟩

theorem C_mul (h : IsChowFormInt I e dl f) {c : k} (hc : c ≠ 0) :
    IsChowFormInt I e dl (C c * f) := by
  refine ⟨?_, (irreducible_isUnit_mul ((IsUnit.mk0 c hc).map C)).2 h.irred, fun u => ?_⟩
  · exact isMultiHomogeneous_iff_block.2
      (IsWeightedHomogeneous.C_mul (isMultiHomogeneous_iff_block.1 h.homog) c)
  · rw [map_mul, aeval_C, mul_eq_zero, map_eq_zero, ← h.zero_iff u]
    simp [hc]

theorem dvd_of_forall_aeval_eq_zero (h : IsChowFormInt I e dl f)
    {p : MvPolynomial (Fin (e + 1) × Fin N) k}
    (hp : ∀ u : Fin (e + 1) × Fin N → AlgebraicClosure k, aeval u f = 0 → aeval u p = 0) :
    f ∣ p := by
  haveI : (Ideal.span {f}).IsPrime := (Ideal.span_singleton_prime h.ne_zero).2 h.irred.prime
  rw [← Ideal.mem_span_singleton,
    ← IsPrime.vanishingIdeal_zeroLocus (K := AlgebraicClosure k) (Ideal.span {f})]
  exact fun u hu => hp u (hu f (Ideal.subset_span rfl))

theorem unique (h : IsChowFormInt I e dl f) (h' : IsChowFormInt I e dl' f') :
    dl = dl' ∧ ∃ c : k, c ≠ 0 ∧ f' = C c * f := by
  have h1 : f ∣ f' := h.dvd_of_forall_aeval_eq_zero fun u hu =>
    (h'.zero_iff u).2 ((h.zero_iff u).1 hu)
  have h2 : f' ∣ f := h'.dvd_of_forall_aeval_eq_zero fun u hu =>
    (h.zero_iff u).2 ((h'.zero_iff u).1 hu)
  obtain ⟨c, hc, hf⟩ := GlobalTheory.Chow.exists_eq_C_mul_of_span_eq
    (Ideal.span_singleton_eq_span_singleton.2 (associated_of_dvd_dvd h1 h2))
  refine ⟨?_, c, hc, hf⟩
  have h3 := (h.C_mul hc).homog
  rw [← hf] at h3
  exact congrFun (GlobalTheory.Chow.IsBlockHomogeneous.unique h'.ne_zero
    (isMultiHomogeneous_iff_block.1 h3) (isMultiHomogeneous_iff_block.1 h'.homog)) 0

theorem span_eq_radical_elimIdeal (h : IsChowFormInt I e dl f)
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) k)) :
    Ideal.span {f} = (GlobalTheory.Chow.elimIdeal (Fin (e + 1)) I).radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure k)]
  refine le_antisymm ?_ fun p hp => ?_
  · rw [Ideal.span_singleton_le_iff_mem]
    exact fun u hu => (h.zero_iff u).2 ((GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u).1 hu)
  · rw [Ideal.mem_span_singleton]
    exact h.dvd_of_forall_aeval_eq_zero fun u hu =>
      hp u ((GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u).2 ((h.zero_iff u).1 hu))

theorem zero_iff_of_isAlgClosed (h : IsChowFormInt I e dl f)
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) k))
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] (u : Fin (e + 1) × Fin N → Ω) :
    MvPolynomial.aeval u f = 0 ↔
      ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, MvPolynomial.aeval y g = 0) ∧
        ∀ i, ∑ j, u (i, j) * y j = 0 := by
  rw [← GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u]
  have hs := h.span_eq_radical_elimIdeal hI
  refine ⟨fun hu p hp => ?_, fun hu => ?_⟩
  · have : p ∈ Ideal.span {f} := hs ▸ Ideal.le_radical hp
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 this
    rw [map_mul, hu, mul_zero]
  · have : f ∈ (GlobalTheory.Chow.elimIdeal (Fin (e + 1)) I).radical := hs ▸ Ideal.subset_span rfl
    obtain ⟨n, hn⟩ := this
    have := hu _ hn
    rw [map_pow] at this
    exact eq_zero_of_pow_eq_zero this

theorem exists_point (h : IsChowFormInt I e dl f) :
    ∃ y : Fin N → AlgebraicClosure k, y ≠ 0 ∧ ∀ g ∈ I, MvPolynomial.aeval y g = 0 := by
  by_contra hc
  refine h.irred.not_isUnit (isUnit_of_dvd_one (h.dvd_of_forall_aeval_eq_zero fun u hu => ?_))
  obtain ⟨y, hy, hI, -⟩ := (h.zero_iff u).1 hu
  exact (hc ⟨y, hy, hI⟩).elim

theorem pos (h : IsChowFormInt I e dl f) : 0 < dl := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  subst h0
  have h1 := (isMultiHomogeneous_iff_block.1 h.homog).isHomogeneous
  simp only [Finset.sum_const_zero] at h1
  have h2 := h1.totalDegree_le
  rw [Nat.le_zero, totalDegree_eq_zero_iff_eq_C] at h2
  refine h.irred.not_isUnit ?_
  rw [h2]
  refine (IsUnit.mk0 _ fun h3 => h.ne_zero ?_).map C
  rw [h2, h3, C_0]

theorem single (h : IsChowFormInt I e dl f) (hp : I.IsPrime)
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) k)) :
    IsChowFormCycle (Finsupp.single I 1) e dl f := by
  refine ⟨1, one_ne_zero, fun _ => dl, fun _ => f, fun P hP => ?_, ?_, ?_⟩
  · obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hP)
    exact ⟨hp, hI, h⟩
  · rw [Finsupp.sum_single_index] <;> simp
  · rw [Finsupp.prod_single_index] <;> simp

end IsChowFormInt

namespace IsChowFormCycle

variable {Z Z' : Ideal (MvPolynomial (Fin N) k) →₀ ℕ} {e dl dl' : ℕ}
  {f f' : MvPolynomial (Fin (e + 1) × Fin N) k}

theorem component (h : IsChowFormCycle Z e dl f) {P : Ideal (MvPolynomial (Fin N) k)}
    (hP : P ∈ Z.support) : P.IsPrime ∧ P.IsHomogeneous (homogeneousSubmodule (Fin N) k) ∧
      ∃ d g, IsChowFormInt P e d g := by
  obtain ⟨c, -, d, g, hg, -, -⟩ := h
  exact ⟨(hg P hP).1, (hg P hP).2.1, d P, g P, (hg P hP).2.2⟩

end IsChowFormCycle

end GlobalTheory.ChowHt
