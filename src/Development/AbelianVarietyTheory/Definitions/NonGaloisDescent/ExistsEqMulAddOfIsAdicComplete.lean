import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TameDescentExtendedActionExtraVector
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

theorem pow_mul_factorial_dvd (l k : ℕ) (hl : 0 < l) : l ^ k * k.factorial ∣ (l * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, hm⟩ : ∃ m, l * (k + 1) = m + 1 := ⟨l * (k + 1) - 1, by
      have : 0 < l * (k + 1) := by positivity
      omega⟩
    have h : (l * k).factorial ∣ m.factorial := Nat.factorial_dvd_factorial (by nlinarith)
    rw [hm, Nat.factorial_succ m, ← hm, Nat.factorial_succ, pow_succ]
    refine Dvd.dvd.trans (dvd_of_eq ?_) (mul_dvd_mul_left (l * (k + 1)) (ih.trans h))
    ring

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) {a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem exists_mul_frob_E : ∃ c ∈ S O K e, c * frob K l (E K l e) = l := by
  have hl := (Fact.out : l.Prime).pos
  have : NeZero (e * l) := ⟨(Nat.mul_pos (NeZero.pos e) hl).ne'⟩
  have hl0 := l_ne_zero (K := K) l
  let c : K⟦X⟧ := expand (e * l) (NeZero.ne _) (rescale (-(l : K)⁻¹) (PowerSeries.mk 1))
  have hc (n : ℕ) : ‖coeff n c‖ * wS K e n ≤ wS K (e * l) n := by
    rw [coeff_expand]
    split_ifs with h
    · obtain ⟨k, rfl⟩ := h
      rw [wS, wS, Nat.mul_div_cancel_left _ (NeZero.pos (e * l)), mul_assoc e l,
        Nat.mul_div_cancel_left _ (NeZero.pos e), coeff_rescale, coeff_mk, Pi.one_apply, mul_one,
        norm_pow, norm_neg, norm_inv, inv_pow, inv_mul_le_iff₀ (pow_pos (norm_pos_iff.2 hl0) k),
        ← norm_pow, ← norm_mul]
      exact_mod_cast norm_natCast_le_of_dvd (K := K) (pow_mul_factorial_dvd l k hl)
    · simpa using wS_nonneg _ _
  refine ⟨c, ⟨fun n => (hc n).trans (wS_le_one _ _), squeeze_zero
    (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n)) hc (tendsto_wS l (e * l))⟩, ?_⟩
  have h := congrArg (fun f => expand (e * l) (NeZero.ne _) (rescale (-(l : K)⁻¹) f))
    (mk_one_mul_one_sub_eq_one K)
  simp only [map_mul, map_sub, map_one, rescale_X, expand_X, expand_C, map_neg] at h
  have h2 : (C (l : K)⁻¹ : K⟦X⟧) * l = 1 := by
    rw [← map_natCast (C : K →+* K⟦X⟧), ← map_mul, inv_mul_cancel₀ hl0, map_one]
  rw [E, map_add, map_pow, frob_X, map_natCast, ← pow_mul, mul_comm l e]
  linear_combination (l : K⟦X⟧) * h - c * X ^ (e * l) * h2

omit [IsUltrametricDist K] in
theorem E_mul_N_Ezpow (j : ℤ) :
    E K l e * N K (Ezpow K l e j) = (j : K⟦X⟧) * N K (E K l e) * Ezpow K l e j := by
  have key (i : ℤ) : N K (Ezpow K l e (i + 1)) =
      Ezpow K l e i * N K (E K l e) + E K l e * N K (Ezpow K l e i) := by
    rw [Ezpow_add, show Ezpow K l e 1 = E K l e from (Ezpow_natCast l e 1).trans (pow_one _),
      Derivation.leibniz]
    rfl
  have h1 (i : ℤ) : Ezpow K l e (i + 1) = Ezpow K l e i * E K l e := by
    rw [Ezpow_add, show Ezpow K l e 1 = E K l e from (Ezpow_natCast l e 1).trans (pow_one _)]
  induction j using Int.induction_on with
  | zero => simp [Ezpow]
  | succ i ih =>
    rw [key, ih, h1]
    push_cast
    ring
  | pred i ih =>
    have h := key (-i - 1)
    have h' := h1 (-i - 1)
    rw [sub_add_cancel] at h h'
    rw [h, h'] at ih
    refine (isUnit_E (K := K) l e).mul_left_cancel ?_
    push_cast at ih ⊢
    linear_combination ih

omit [IsUltrametricDist K] in
theorem Ezpow_neg_mul (j : ℤ) : Ezpow K l e (-j) * Ezpow K l e j = 1 := by
  rw [← Ezpow_add]
  simp [Ezpow]

variable {l e}

variable [CompleteSpace K]

end GlobalTheory.BK
