import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.S3x1

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Blocks

variable {A : Type} {r k : ℕ}

variable [CommRing A]

structure GP (P : Matrix (Fin k) (Fin k) A → Prop) : Prop where
  one : P 1
  mul : ∀ {h h'}, P h → P h' → P (h * h')
  inv : ∀ {h}, P h → P h⁻¹
  unit : ∀ {h}, P h → IsUnit h.det

variable {P : Matrix (Fin k) (Fin k) A → Prop}

theorem uni_unit {n : ℕ} {u : Matrix (Fin n) (Fin n) A} (hu : IsUpUni u) : IsUnit u.det := by
  rw [isUpUni_det A hu]; exact isUnit_one

end Blocks

end Formalism.FourierDecayAlt.P.S3x1

namespace Formalism.FourierDecayAlt.P.S3x1

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Count

theorem card_lt_pairs (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  have h : ∀ j : Fin n, ∑ i : Fin n, (if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have e : Finset.filter (fun i : Fin n => i < j) Finset.univ = Finset.Iio j := by ext i; simp
    rw [e, Fin.card_Iio]
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

variable {A : Type} [CommRing A]

def uniEquiv (n : ℕ) : {u : Matrix (Fin n) (Fin n) A // IsUpUni u} ≃ ({p : Fin n × Fin n // p.1 < p.2} → A) where
  toFun u := fun p => u.1 p.1.1 p.1.2
  invFun f := ⟨Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0, by
    constructor
    · intro i j hij
      have hij' : j < i := hij
      simp [not_lt.2 hij'.le, hij'.ne']
    · intro a; simp⟩
  left_inv u := by
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h]
    · subst h; simp [u.2.2 i]
    · have : u.1 i j = 0 := u.2.1 h
      simp [not_lt.2 h.le, h.ne', this]
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    have h' : i < j := h
    simp [h']

theorem card_uni (K : Type) [Field K] [Fintype K] (n : ℕ) :
    Nat.card {u : Matrix (Fin n) (Fin n) K // IsUpUni u} = Fintype.card K ^ (n * (n - 1) / 2) := by
  rw [Nat.card_congr (uniEquiv n), Nat.card_fun, card_lt_pairs, Nat.card_eq_fintype_card]

noncomputable def upUniGEquiv (n : ℕ) : upUniG A n ≃ {u : Matrix (Fin n) (Fin n) A // IsUpUni u} where
  toFun g := ⟨g.1.1, g.2⟩
  invFun u := ⟨Matrix.GeneralLinearGroup.mk'' u.1 (uni_unit u.2), u.2⟩
  left_inv g := Subtype.ext (Units.ext rfl)
  right_inv u := rfl

variable {r k : ℕ}

end Count

end Formalism.FourierDecayAlt.P.S3x1

namespace Formalism.FourierDecayAlt.P.S3x1

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Count2

variable {A : Type} [CommRing A] {r k : ℕ}

theorem prod_gl (q k : ℕ) : ∏ i : Fin k, (q ^ k - q ^ (i : ℕ)) =
    q ^ (k * (k - 1) / 2) * ∏ i ∈ Icc 1 k, (q ^ i - 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ k - q ^ i) k, ← Finset.sum_range_id,
    ← Finset.prod_pow_eq_pow_sum]
  have h1 : ∏ i ∈ Icc 1 k, (q ^ i - 1) = ∏ i ∈ range k, (q ^ (k - i) - 1) := by
    refine Finset.prod_nbij' (fun i => k - i) (fun i => k - i) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      have : k - (k - a) = a := by omega
      rw [this]
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i ≤ k := (Finset.mem_range.1 hi).le
  rw [Nat.mul_sub, ← pow_add, Nat.add_sub_cancel' hi', mul_one]

end Count2

end Formalism.FourierDecayAlt.P.S3x1

open Formalism.FourierDecayAlt.P.S3x1 in
theorem Formalism.FourierDecayAlt.P.gamma_factor_product : Formalism.FourierDecayAlt.S3.GammaProduct := by
  intro K _ _ k
  rw [Matrix.card_GL_field, Nat.card_congr (upUniGEquiv k), card_uni, prod_gl]

