import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAddOfLt

namespace GlobalTheory.TorsionIntegral

open IsUltrametricDist WeierstrassCurve

variable {K : Type} [NormedField K] [IsUltrametricDist K]

lemma norm_sub_le_max' (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have := norm_add_le_max a (-b)
  rwa [norm_neg, ← sub_eq_add_neg] at this

lemma norm_add_eq_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

lemma norm_y_sq {A B x y : K} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hx : 1 < ‖x‖)
    (h : y ^ 2 = x ^ 3 + A * x + B) : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
  have h1 : ‖x‖ < ‖x‖ ^ 3 := by
    have := pow_lt_pow_right₀ hx (show 1 < 3 by norm_num)
    simpa using this
  rw [← norm_pow, h, add_assoc, norm_add_eq_of_lt, norm_pow]
  rw [norm_pow]
  refine (norm_add_le_max _ _).trans_lt (max_lt ?_ (by linarith))
  rw [norm_mul]
  nlinarith [norm_nonneg A]

lemma norm_sum_three_le (a b c : K) : ‖a + b + c‖ ≤ max (max ‖a‖ ‖b‖) ‖c‖ :=
  (norm_add_le_max _ _).trans (max_le_max (norm_add_le_max _ _) le_rfl)

lemma norm_two_le : ‖(2 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 2

lemma norm_three_le : ‖(3 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 3

noncomputable def param {W : Affine K} : W.Point → K
  | .zero => 0
  | .some x y _ => x / y

def Near {W : Affine K} (M : ℝ) : W.Point → Prop
  | .zero => True
  | .some x _ _ => M ≤ ‖x‖

lemma add_step [DecidableEq K] {A B : K} {M : ℝ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hM : 1 < M)
    (P Q : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Point) (hP : Near M P)
    (hQ : Near M Q) : Near M (P + Q) ∧ ‖param (P + Q) - param P - param Q‖ ≤ M⁻¹ := by
  first
  | exact @_root_.GlobalTheory.UltrametricLineBounds.large_add
  | exact _root_.GlobalTheory.UltrametricLineBounds.large_add
  | (apply _root_.GlobalTheory.UltrametricLineBounds.large_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricLineBounds.large_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricLineBounds.large_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricLineBounds.large_add ..)

theorem norm_x_le_one_of_nsmul_eq_zero (K : Type) [NormedField K] [IsUltrametricDist K]
    [DecidableEq K] (A B : K) (N : ℕ) (x y : K)
    (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hN : ‖(N : K)‖ = 1)
    (h0 : N • (WeierstrassCurve.Affine.Point.some x y h) = 0) : ‖x‖ ≤ 1 := by
  by_contra hx
  push Not at hx
  have M0 : 0 ≤ ‖x‖⁻¹ := by positivity
  have hP : Near ‖x‖ (Affine.Point.some x y h) := le_refl _
  have key : ∀ k : ℕ, Near ‖x‖ (k • Affine.Point.some x y h) ∧
      ‖param (k • Affine.Point.some x y h) - (k : K) * (x / y)‖ ≤ ‖x‖⁻¹ := by
    intro k
    induction k with
    | zero =>
      rw [zero_nsmul]
      exact ⟨trivial, by simp [Affine.Point.zero_def, param]⟩
    | succ k ih =>
      obtain ⟨s1, s2⟩ := add_step hA hB hx _ _ ih.1 hP
      rw [succ_nsmul]
      refine ⟨s1, ?_⟩
      have := (norm_add_le_max _ _).trans (max_le s2 ih.2)
      refine le_of_eq_of_le (congrArg norm ?_) this
      simp only [param]
      push_cast
      ring
  have h1 := (key N).2
  rw [h0] at h1
  simp only [Affine.Point.zero_def, param, zero_sub, norm_neg, norm_mul, hN, one_mul,
    norm_div] at h1
  have he : y ^ 2 = x ^ 3 + A * x + B := by
    have := (Affine.equation_iff _ _).1 h.1
    simp only at this
    linear_combination this
  have hy := norm_y_sq hA hB hx he
  have x0 : 0 < ‖x‖ := by linarith
  have y0 : 0 < ‖y‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) fun h => ?_
    rw [← h] at hy
    have : 0 < ‖x‖ ^ 3 := by positivity
    simp at hy
    linarith
  rw [inv_eq_one_div, div_le_div_iff₀ y0 x0, one_mul] at h1
  have h2 : (‖x‖ * ‖x‖) ^ 2 ≤ ‖y‖ ^ 2 := by gcongr
  rw [hy] at h2
  have : ‖x‖ ^ 3 * 1 < ‖x‖ ^ 3 * ‖x‖ := by gcongr
  nlinarith

end GlobalTheory.TorsionIntegral
