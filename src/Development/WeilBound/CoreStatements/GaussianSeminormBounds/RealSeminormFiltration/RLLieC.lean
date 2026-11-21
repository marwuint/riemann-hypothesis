import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupGeneratedByExp

noncomputable section

open Complex Matrix Filter Topology

namespace PositivityTheory.RL.Up

theorem exp_mul_inj {z z' : ℂ} (h : ∀ t : ℝ, cexp (z * t) = cexp (z' * t)) : z = z' := by
  have d : ∀ z : ℂ, HasDerivAt (fun t : ℝ => cexp (z * t)) z 0 := fun z => by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul z).cexp
  have := d z
  simp only [h] at this
  exact this.unique (d z')

section Banach

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

def expU (Z : 𝔸) : 𝔸ˣ :=
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  ⟨NormedSpace.exp Z, NormedSpace.exp (-Z),
    by rw [← NormedSpace.exp_add_of_commute (Commute.refl Z).neg_right, add_neg_cancel, NormedSpace.exp_zero],
    by rw [← NormedSpace.exp_add_of_commute (Commute.refl Z).neg_left, neg_add_cancel, NormedSpace.exp_zero]⟩

theorem expU_add (Z : 𝔸) (s t : ℝ) : expU ((s + t) • Z) = expU (s • Z) * expU (t • Z) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  refine Units.ext ?_
  show NormedSpace.exp _ = NormedSpace.exp _ * NormedSpace.exp _
  rw [add_smul, NormedSpace.exp_add_of_commute (((Commute.refl Z).smul_left s).smul_right t)]

theorem expU_zero : expU (0 : 𝔸) = 1 := Units.ext NormedSpace.exp_zero

theorem continuous_expU (Z : 𝔸) : Continuous fun t : ℝ => expU (t • Z) :=
  Units.isOpenEmbedding_val.isInducing.continuous_iff.2
    (continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) Z t).continuousAt)

end Banach

theorem eq_trace {β : Type} [Fintype β] [DecidableEq β] (ξ : Matrix β β ℂ →ₗ[ℂ] ℂ)
    (h : ∀ A B, ξ (A * B - B * A) = 0) : ∃ c : ℂ, ∀ A, ξ A = c * A.trace := by
  rcases isEmpty_or_nonempty β with hβ | ⟨⟨b⟩⟩
  · exact ⟨0, fun A => by rw [Subsingleton.elim A 0, map_zero, zero_mul]⟩
  refine ⟨ξ (single b b 1), fun A => ?_⟩
  have h1 : ∀ i j, i ≠ j → ξ (single i j 1) = 0 := fun i j hij => by
    have := h (single i i 1) (single i j 1)
    rwa [single_mul_single_same, single_mul_single_of_ne (h := hij.symm), one_mul, sub_zero] at this
  have h2 : ∀ i, ξ (single i i 1) = ξ (single b b 1) := fun i => by
    have := h (single i b 1) (single b i 1)
    rwa [single_mul_single_same, single_mul_single_same, one_mul, map_sub, sub_eq_zero] at this
  conv_lhs => rw [matrix_eq_sum_single A]
  simp only [map_sum]
  rw [Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∀ j, ξ (single i j (A i j)) = A i j * ξ (single i j 1) := fun j => by
    rw [← smul_eq_mul, ← map_smul, smul_single, smul_eq_mul, mul_one]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [e, h1 i j hj.symm, mul_zero]) (by simp), e, h2, mul_comm]
  rfl

theorem real_form_trace {β : Type} [Fintype β] [DecidableEq β] (τ : Matrix β β ℂ →ₗ[ℝ] Matrix β β ℂ)
    (hI : ∀ A, τ (I • A) = -(I • τ A)) (hτ : ∀ A, τ (τ A) = A) (ζ : Matrix β β ℂ →ₗ[ℝ] ℂ)
    (hb : ∀ X Y, τ X = X → τ Y = Y → τ (X * Y - Y * X) = X * Y - Y * X ∧ ζ (X * Y - Y * X) = 0) :
    ∃ c : ℂ, ∀ Z, τ Z = Z → ζ Z = c * Z.trace := by
  let P : Matrix β β ℂ → Matrix β β ℂ := fun A => (1 / 2 : ℝ) • (A + τ A)
  have hP : ∀ A, τ (P A) = P A := fun A => by simp only [P, map_smul, map_add, hτ, add_comm]
  let ξ0 : Matrix β β ℂ → ℂ := fun A => ζ (P A) - I * ζ (P (I • A))
  have add : ∀ A B, ξ0 (A + B) = ξ0 A + ξ0 B := fun A B => by
    simp only [ξ0, P, smul_add, map_add, map_smul]
    ring
  have rs : ∀ (r : ℝ) A, ξ0 (r • A) = r * ξ0 A := fun r A => by
    simp only [ξ0, P, smul_comm I r, smul_add, map_add, map_smul, real_smul]
    ring
  have is : ∀ A, ξ0 (I • A) = I * ξ0 A := fun A => by
    simp only [ξ0, P, smul_smul, I_mul_I, neg_smul, one_smul, smul_add, map_add, map_smul, map_neg, real_smul, smul_neg]
    linear_combination ((((1 / 2 : ℝ) : ℂ) * ζ (I • A) + ((1 / 2 : ℝ) : ℂ) * ζ (τ (I • A)))) * I_mul_I
  let ξ : Matrix β β ℂ →ₗ[ℂ] ℂ :=
    { toFun := ξ0
      map_add' := add
      map_smul' := fun c A => by
        have e : c • A = c.re • A + I • (c.im • A) := by
          ext i j
          simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, real_smul]
          linear_combination (-A i j) * re_add_im c
        rw [e, add, is, rs, rs, RingHom.id_apply, smul_eq_mul]
        linear_combination (ξ0 A) * re_add_im c }
  have fix : ∀ Z, τ Z = Z → ξ Z = ζ Z := fun Z hZ => by
    have e1 : P Z = Z := by
      simp only [P, hZ]
      module
    have e2 : P (I • Z) = 0 := by simp only [P, hI, hZ, add_neg_cancel, smul_zero]
    show ζ (P Z) - I * ζ (P (I • Z)) = _
    rw [e1, e2, map_zero, mul_zero, sub_zero]
  have dec : ∀ A, A = P A - I • P (I • A) := fun A => by
    simp only [P, hI]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul, real_smul]
    push_cast
    linear_combination ((A i j - τ A i j) / 2) * I_mul_I
  have br : ∀ X Y, τ X = X → τ Y = Y → ξ (X * Y - Y * X) = 0 := fun X Y hX hY => by
    rw [fix _ (hb X Y hX hY).1, (hb X Y hX hY).2]
  obtain ⟨c, hc⟩ := eq_trace ξ fun A B => by
    have h1 : ∀ X, τ X = X → ξ (X * B - B * X) = 0 := fun X hX => by
      have e : X * B - B * X = (X * P B - P B * X) - I • (X * P (I • B) - P (I • B) * X) := by
        conv_lhs => rw [dec B]
        simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        abel
      rw [e, map_sub, map_smul, br _ _ hX (hP _), br _ _ hX (hP _), smul_zero, sub_zero]
    have e : A * B - B * A = (P A * B - B * P A) - I • (P (I • A) * B - B * P (I • A)) := by
      conv_lhs => rw [dec A]
      simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      abel
    rw [e, map_sub, map_smul, h1 _ (hP _), h1 _ (hP _), smul_zero, sub_zero]
  exact ⟨c, fun Z hZ => by rw [← fix Z hZ, hc]⟩

end PositivityTheory.RL.Up

end
