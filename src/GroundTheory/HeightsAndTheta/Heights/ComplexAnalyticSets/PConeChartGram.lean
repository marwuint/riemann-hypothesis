import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartGram
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeChartArea

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets

noncomputable section

theorem le_of_ringKrullDim_quotient {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) : e + 1 ≤ n := by
  have h := ringKrullDim_quotient_le J
  rw [hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  exact_mod_cast h

theorem coneBall_hausdorff_lt_top (hMF : MassFinite.Statement) {n e : ℕ} (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0} < ⊤ := by
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det
  let P : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 h.matᵀ)
  let Q : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 (h.matᵀ)⁻¹)
  have hsub : {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0} ⊆
      Q '' (zeroSetEuc J ∩ ball 0 (‖P‖ + 1)) := by
    rintro z ⟨hz, hzJ⟩
    refine ⟨P z, ⟨fun q hq => hzJ q hq, ?_⟩, ?_⟩
    · rw [mem_ball_zero_iff]
      calc ‖P z‖ ≤ ‖P‖ * ‖z‖ := P.le_opNorm z
        _ ≤ ‖P‖ * 1 := by gcongr
        _ < ‖P‖ + 1 := by linarith
    · ext i
      simp [P, Q, Matrix.toLpLin_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet]
  have hd : (0 : ℝ) ≤ ((2 * (e + 1) : ℕ) : ℝ) := by positivity
  calc _ ≤ Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (Q '' (zeroSetEuc J ∩ ball 0 (‖P‖ + 1))) :=
        measure_mono hsub
    _ ≤ (‖Q‖₊ : ENNReal) ^ ((2 * (e + 1) : ℕ) : ℝ) *
          Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (zeroSetEuc J ∩ ball 0 (‖P‖ + 1)) :=
        Q.lipschitz.hausdorffMeasure_image_le hd _
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hd ENNReal.coe_ne_top)
        (hMF n (e + 1) J hJ (by exact_mod_cast hdim) _)

theorem integral_line_gram {n : ℕ} (e : ℕ) (h : HermNorm n) (g : (Fin n → ℂ) → ℝ)
    (hg : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x) (x : Fin n → ℂ) (hx : x ≠ 0) (G : ℝ) :
    ∫ t : ℂ, (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => g (h.pointOf z))
          (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G) =
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
        (g x * ((e.factorial : ℝ) / Real.pi ^ e * G / h.dualNorm x ^ (2 * (e + 1)))) := by
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det
  have hinv : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hMx : (h.matᵀ)⁻¹ *ᵥ x ≠ 0 := by
    intro h0
    apply hx
    rw [← hinv, h0, Matrix.mulVec_zero]
  set ρ := ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ with hρ_def
  have hρx : h.dualNorm x = ρ := by
    rw [hρ_def, EuclideanSpace.norm_eq]
    rfl
  have hρ : 0 < ρ := by
    rw [hρ_def, norm_pos_iff]
    intro h0
    exact hMx (by simpa using congrArg WithLp.ofLp h0)
  have hpt : ∀ t : ℂ, h.pointOf (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) = t • x := by
    intro t
    have : (fun i => (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) i) = t • ((h.matᵀ)⁻¹ *ᵥ x) := by
      ext i
      simp
    simp only [HermNorm.pointOf, this, Matrix.mulVec_smul, hinv]
  have hae : (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => g (h.pointOf z)) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) =ᵐ[volume]
      fun t => (g x * G) * (ball (0 : ℂ) (1 / ρ)).indicator (fun t => ‖t‖ ^ (2 * e)) t := by
    have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with t ht
    have hiff : ‖t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ < 1 ↔ ‖t‖ < 1 / ρ := by
      rw [norm_smul, lt_div_iff₀ hρ]
    by_cases hb : ‖t‖ < 1 / ρ
    · rw [indicator_of_mem (mem_ball_zero_iff.2 (hiff.2 hb)),
        indicator_of_mem (mem_ball_zero_iff.2 hb), hpt, hg t x ht]
      ring
    · rw [indicator_of_notMem (fun h => hb (hiff.1 (mem_ball_zero_iff.1 h))),
        indicator_of_notMem (fun h => hb (mem_ball_zero_iff.1 h))]
      ring
  rw [integral_congr_ae hae, integral_const_mul,
    integral_indicator_ball_norm_pow e (by positivity), hρx]
  rw [one_div, inv_pow, Nat.factorial_succ]
  have hρ' : ρ ^ (2 * (e + 1)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights
