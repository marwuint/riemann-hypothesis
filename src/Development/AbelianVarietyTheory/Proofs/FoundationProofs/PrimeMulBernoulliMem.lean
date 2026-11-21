import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

open Finset GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.EisCong

variable {K : Type} [Field K] [CharZero K]

def pInt (p : ℕ) [Fact p.Prime] (K : Type) [Field K] : Subring K where
  carrier := {x | ∃ D : ℕ, ¬ p ∣ D ∧ IsIntegral ℤ ((D : K) * x)}
  mul_mem' := by
    rintro x y ⟨D, hD, hx⟩ ⟨E, hE, hy⟩
    refine ⟨D * E, fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hD hE, ?_⟩
    have : ((D * E : ℕ) : K) * (x * y) = ((D : K) * x) * ((E : K) * y) := by push_cast; ring
    rw [this]; exact hx.mul hy
  one_mem' := ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using isIntegral_one⟩
  add_mem' := by
    rintro x y ⟨D, hD, hx⟩ ⟨E, hE, hy⟩
    refine ⟨D * E, fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hD hE, ?_⟩
    have : ((D * E : ℕ) : K) * (x + y) = (E : K) * ((D : K) * x) + (D : K) * ((E : K) * y) := by
      push_cast; ring
    rw [this]
    exact ((isIntegral_natCast E).mul hx).add ((isIntegral_natCast D).mul hy)
  zero_mem' := ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using isIntegral_zero⟩
  neg_mem' := by
    rintro x ⟨D, hD, hx⟩
    exact ⟨D, hD, by rw [mul_neg]; exact hx.neg⟩

variable {p : ℕ} [Fact p.Prime]

omit [CharZero K] in
lemma mem_of_isIntegral {x : K} (h : IsIntegral ℤ x) : x ∈ pInt p K :=
  ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using h⟩

lemma inv_nat_mem {m : ℕ} (h : ¬ p ∣ m) : (m : K)⁻¹ ∈ pInt p K := by
  have hm : (m : K) ≠ 0 := by
    have : m ≠ 0 := by rintro rfl; exact h (dvd_zero _)
    exact_mod_cast this
  exact ⟨m, h, by rw [mul_inv_cancel₀ hm]; exact isIntegral_one⟩

lemma inv_int_mem {c : ℤ} (h : ¬ (p : ℤ) ∣ c) : (c : K)⁻¹ ∈ pInt p K := by
  have h1 : ((c.natAbs : ℕ) : K)⁻¹ ∈ pInt p K := inv_nat_mem (fun h' => h (Int.natCast_dvd.2 h'))
  rcases Int.natAbs_eq c with h2 | h2
  · rw [h2]; simpa using h1
  · rw [h2]; simpa using neg_mem h1

omit [CharZero K] in
lemma root_zpow_mem {ζ : K} {M : ℕ} (hM : 0 < M) (h : IsPrimitiveRoot ζ M) (e : ℤ) : ζ ^ e ∈ pInt p K := by
  rcases e with e | e
  · simpa using pow_mem (mem_of_isIntegral (h.isIntegral hM)) e
  · rw [zpow_negSucc, ← inv_pow]; exact pow_mem (mem_of_isIntegral (h.inv.isIntegral hM)) _

lemma pow_div_mem {k e : ℕ} (hk : k ≠ 0) (h : k < p ^ (e + 1)) : (p : K) ^ e / k ∈ pInt p K := by
  have hp : p.Prime := Fact.out
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk p hp.ne_one
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero _)
  have hv : v ≤ e := by
    have : p ^ v < p ^ (e + 1) := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)) h
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).1 this
    omega
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hv
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have : (p : K) ^ (v + w) / ((p ^ v * u : ℕ) : K) = (p : K) ^ w * (u : K)⁻¹ := by
    push_cast; field_simp; ring
  rw [this]
  exact mul_mem (pow_mem (natCast_mem _ p) w) (inv_nat_mem hu)

lemma pow_div_add_two_mem (hp2 : p ≠ 2) (n i : ℕ) : ((p : K) ^ (n + 1)) ^ i / ((i : K) + 2) ∈ pInt p K := by
  have hp : p.Prime := Fact.out
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have h1 : ∀ i : ℕ, i + 2 < 3 ^ (i + 1) := by
    intro i
    induction i with
    | zero => norm_num
    | succ i ih => rw [pow_succ]; omega
  have h2 : i + 2 < p ^ ((n + 1) * i + 1) :=
    (h1 i).trans_le ((Nat.pow_le_pow_left h3 _).trans (Nat.pow_le_pow_right hp.pos (by nlinarith)))
  have := pow_div_mem (K := K) (k := i + 2) (by omega) h2
  rw [← pow_mul]
  simpa using this

lemma prime_mul_bernoulli_mem (k : ℕ) : (p : K) * ((bernoulli (k + 2) : ℚ) : K) ∈ pInt p K := by
  have hp : p.Prime := Fact.out
  rcases Nat.even_or_odd (k + 2) with ⟨m, hm⟩ | hodd
  · have hk2 : k + 2 = 2 * m := by omega
    obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen m
    have hB : bernoulli (k + 2) = (z : ℚ) -
        ∑ q ∈ Finset.range (2 * m + 2) with q.Prime ∧ (q - 1) ∣ 2 * m, (1 : ℚ) / q := by
      rw [hk2, hz]; ring
    rw [hB]
    push_cast
    rw [mul_sub, Finset.mul_sum]
    refine sub_mem (mul_mem (natCast_mem _ _) (intCast_mem _ _)) (sum_mem fun q hq => ?_)
    have hq' := (Finset.mem_filter.mp hq).2.1
    by_cases hql : q = p
    · subst hql
      have : (q : K) ≠ 0 := by exact_mod_cast hp.ne_zero
      rw [mul_one_div_cancel this]; exact one_mem _
    · rw [one_div]
      exact mul_mem (natCast_mem _ _)
        (inv_nat_mem fun h => hql ((Nat.prime_dvd_prime_iff_eq hp hq').mp h).symm)
  · rw [bernoulli_eq_zero_of_odd hodd (by omega)]
    simp

lemma choose_cast (m i : ℕ) :
    (((m + 2).choose (i + 2) : ℕ) : K) = ((m : K) + 2) * ((m + 1).choose (i + 1) : ℕ) / ((i : K) + 2) := by
  have h := Nat.add_one_mul_choose_eq (m + 1) (i + 1)
  have hi : (i : K) + 2 ≠ 0 := by exact_mod_cast (show i + 2 ≠ 0 by omega)
  rw [eq_div_iff hi]
  have h' := congrArg (Nat.cast : ℕ → K) h
  push_cast at h'
  simp only [add_assoc, one_add_one_eq_two] at h'
  rw [← h']

lemma binom_second (hp2 : p ≠ 2) (n m : ℕ) (x t : ℤ) :
    ∃ y ∈ pInt p K, ((x : K) + t * (p : K) ^ (n + 1)) ^ (m + 2) =
      (x : K) ^ (m + 2) + ((m : K) + 2) * t * (p : K) ^ (n + 1) * (x : K) ^ (m + 1) +
        ((m : K) + 2) * ((p : K) ^ (n + 1)) ^ 2 * y := by
  set Q : K := (p : K) ^ (n + 1) with hQ
  refine ⟨∑ i ∈ range (m + 1), (t : K) ^ (i + 2) * (x : K) ^ (m - i) * ((m + 1).choose (i + 1) : ℕ) *
    (Q ^ i / ((i : K) + 2)), sum_mem fun i _ => mul_mem (mul_mem (mul_mem (pow_mem (intCast_mem _ _) _)
      (pow_mem (intCast_mem _ _) _)) (natCast_mem _ _)) (pow_div_add_two_mem hp2 n i), ?_⟩
  rw [add_comm (x : K), add_pow, sum_range_succ', sum_range_succ', mul_sum]
  have : ∀ i ∈ range (m + 1), ((t : K) * Q) ^ (i + 1 + 1) * (x : K) ^ (m + 2 - (i + 1 + 1)) *
      ((m + 2).choose (i + 1 + 1) : ℕ) = ((m : K) + 2) * Q ^ 2 * ((t : K) ^ (i + 2) * (x : K) ^ (m - i) *
        ((m + 1).choose (i + 1) : ℕ) * (Q ^ i / ((i : K) + 2))) := by
    intro i _
    rw [show m + 2 - (i + 1 + 1) = m - i by omega, show i + 1 + 1 = i + 2 by omega, choose_cast]
    ring
  rw [sum_congr rfl this]
  simp
  ring

lemma binom_first (Q : ℤ) (k : ℕ) (x t : ℤ) :
    ∃ y : ℤ, ((x : K) + t * (Q : K)) ^ k = (x : K) ^ k + Q * y := by
  obtain ⟨y, hy⟩ := sub_dvd_pow_sub_pow (x + t * Q) x k
  refine ⟨t * y, ?_⟩
  have := congrArg (Int.cast : ℤ → K) hy
  push_cast at this ⊢
  linear_combination this

end GlobalTheory.EisCong
