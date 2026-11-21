import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeE
import Mathlib
import Formalism.CyclotomicNorms.StatementT
import Formalism.CyclotomicNorms.NonsquarefreeBounds.IrreducibilityOfRestriction

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open MonoidAlgebra

attribute [local instance] Classical.propDecidable

section Triv

variable (K : Type) [Field K] (Γ : Type) [Group Γ] [Finite Γ]

def eT : MonoidAlgebra K Γ := MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun _ => ((Nat.card Γ : K))⁻¹

variable {K Γ}

theorem eT_coeff (g : Γ) : (eT K Γ).coeff g = ((Nat.card Γ : K))⁻¹ := rfl

theorem card_ne [CharZero K] : (Nat.card Γ : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'

theorem eT_idem [CharZero K] : eT K Γ * eT K Γ = eT K Γ := by
  have := Fintype.ofFinite Γ
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [coeff_mul_fintype]
  simp only [eT_coeff, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [← mul_assoc, mul_inv_cancel₀ card_ne, one_mul]

theorem eT_central (a : MonoidAlgebra K Γ) : eT K Γ * a = a * eT K Γ :=
  commute_of_single _ (fun g => by
    apply MonoidAlgebra.coeff_injective
    ext h
    rw [coeff_mul_single_apply, coeff_single_mul_apply, eT_coeff, eT_coeff, mul_one, one_mul]) a

theorem eT_ne_zero [CharZero K] : eT K Γ ≠ 0 := fun h =>
  inv_ne_zero (card_ne (K := K) (Γ := Γ)) (congrArg (fun x => x.coeff 1) h)

theorem one_sub_eT_ne_zero [CharZero K] (g : Γ) (hg : g ≠ 1) : 1 - eT K Γ ≠ 0 := fun h => by
  have h1 := congrArg (fun x => x.coeff g) h
  simp only [coeff_sub, Finsupp.sub_apply, eT_coeff, one_def, MonoidAlgebra.coeff_single_apply, if_neg (Ne.symm hg),
    zero_sub] at h1
  exact inv_ne_zero (card_ne (K := K) (Γ := Γ)) (neg_eq_zero.mp h1)

end Triv

section Family

variable (K : Type) [Field K] (Γ : Type) {Λ : Type} [Group Γ] [Finite Γ] (fA fB : Λ)

def esZ (f : Λ) : MonoidAlgebra K Γ := if f = fA then 1 - eT K Γ else if f = fB then eT K Γ else 0

def cfQ (f : Λ) (h : Γ) : ℚ :=
  if f = fA then (if (1 : Γ) = h then 1 else 0) - ((Nat.card Γ : ℚ))⁻¹
  else if f = fB then ((Nat.card Γ : ℚ))⁻¹ else 0

theorem esZ_coeff [CharZero K] (f : Λ) (h : Γ) : (esZ K Γ fA fB f).coeff h = (cfQ Γ fA fB f h : K) := by
  unfold esZ cfQ
  split_ifs <;> simp [eT_coeff, one_def, MonoidAlgebra.coeff_single_apply, *]

variable {K Γ fA fB} [CharZero K] (hAB : fA ≠ fB)

theorem esZ_idem (f : Λ) : esZ K Γ fA fB f * esZ K Γ fA fB f = esZ K Γ fA fB f := by
  unfold esZ
  split_ifs
  · rw [sub_mul, mul_sub, mul_sub, eT_idem, one_mul, one_mul, mul_one, sub_self, sub_zero]
  · exact eT_idem
  · simp

omit [CharZero K] in
theorem esZ_central (f : Λ) (a) : esZ K Γ fA fB f * a = a * esZ K Γ fA fB f := by
  unfold esZ
  split_ifs
  · rw [sub_mul, mul_sub, eT_central, one_mul, mul_one]
  · exact eT_central a
  · simp

theorem esZ_orth (f f' : Λ) (h : f ≠ f') : esZ K Γ fA fB f * esZ K Γ fA fB f' = 0 := by
  unfold esZ
  split_ifs with h1 h2' h3 h4 h5 h6
  · exact absurd (h1.trans h2'.symm) h
  · rw [sub_mul, eT_idem, one_mul, sub_self]
  · simp
  · rw [mul_sub, eT_idem, mul_one, sub_self]
  · exact absurd (h4.trans h6.symm) h
  all_goals simp

omit [CharZero K] in
include hAB in
theorem esZ_sum (S : Finset Λ) (hA : fA ∈ S) (hB : fB ∈ S) : ∑ f ∈ S, esZ K Γ fA fB f = 1 := by
  have e : ∀ f, esZ K Γ fA fB f = (if f = fA then 1 - eT K Γ else 0) + if f = fB then eT K Γ else 0 := fun f => by
    unfold esZ
    by_cases h1 : f = fA
    · rw [if_pos h1, if_pos h1, if_neg (fun h => hAB (h1.symm.trans h)), add_zero]
    · rw [if_neg h1, if_neg h1, zero_add]
  simp only [e]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos hA, if_pos hB, sub_add_cancel]

end Family

end Formalism.BasicNotions.Examples₂.NZ
