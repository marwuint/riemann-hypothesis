import Mathlib

namespace ZbYha7

open scoped ComplexOrder in
private lemma pos {I : Type} [Fintype I] (A : Matrix I I ℂ) (hA : A.PosDef) (x : I → ℂ) (hx : x ≠ 0) :
    0 < RCLike.re (star x ⬝ᵥ A.mulVec x) :=
  (RCLike.pos_iff.mp (hA.dotProduct_mulVec_pos hx)).1

private lemma scale {I : Type} [Fintype I] (A : Matrix I I ℂ) (x : I → ℂ) (r : ℝ) :
    RCLike.re (star ((r : ℂ) • x) ⬝ᵥ A.mulVec ((r : ℂ) • x)) = r ^ 2 * RCLike.re (star x ⬝ᵥ A.mulVec x) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
  simp only [smul_eq_mul, RCLike.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul]
  simp [sq]

private lemma cont {I : Type} [Fintype I] (A : Matrix I I ℂ) :
    Continuous fun x : I → ℂ => RCLike.re (star x ⬝ᵥ A.mulVec x) := by
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

end ZbYha7

open scoped ComplexOrder in
theorem UpperTheory.Reformulated.B.Yha7.main
    {I : Type} [inst : Fintype I] [DecidableEq I] (A : Matrix I I ℂ) :
    A.PosDef → ∃ l : ℝ, 0 < l ∧ ∀ x : I → ℂ, l * ‖x‖ ^ 2 ≤ RCLike.re (star x ⬝ᵥ A.mulVec x) := by
  intro hA
  set f : (I → ℂ) → ℝ := fun x => RCLike.re (star x ⬝ᵥ A.mulVec x) with hf
  have hpos : ∀ x : I → ℂ, x ≠ 0 → 0 < f x := ZbYha7.pos A hA
  have hS : ∃ l : ℝ, 0 < l ∧ ∀ y ∈ Metric.sphere (0 : I → ℂ) 1, l ≤ f y := by
    by_cases hne : (Metric.sphere (0 : I → ℂ) 1).Nonempty
    · obtain ⟨y0, hy0, hmin⟩ := (isCompact_sphere (0 : I → ℂ) 1).exists_isMinOn hne
        (ZbYha7.cont A).continuousOn
      refine ⟨f y0, hpos y0 ?_, fun y hy => hmin hy⟩
      intro h; rw [h] at hy0; simp at hy0
    · exact ⟨1, one_pos, fun y hy => (hne ⟨y, hy⟩).elim⟩
  obtain ⟨l, hl, hlS⟩ := hS
  refine ⟨l, hl, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; simp
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set y : I → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hy
  have hyS : y ∈ Metric.sphere (0 : I → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, hy, norm_smul]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    field_simp
  have h1 := hlS y hyS
  have hxy : x = ((‖x‖ : ℝ) : ℂ) • y := by
    rw [hy, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  have h2 : f x = ‖x‖ ^ 2 * f y := by
    conv_lhs => rw [hxy]
    exact ZbYha7.scale A y ‖x‖
  change l * ‖x‖ ^ 2 ≤ f x
  rw [h2, mul_comm l]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)
