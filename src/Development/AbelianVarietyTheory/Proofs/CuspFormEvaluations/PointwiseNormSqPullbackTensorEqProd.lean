import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupLeL2PrincipalTorus
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardToMultisetEqDegree

open Complex ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

namespace ThetaBound

section General

variable {ι : Type} [Fintype ι]

theorem l2NormSq_nonneg_gaussianTorus (Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : 0 ≤ Y.l2 q F := by
  unfold GT.l2
  rw [MeasureTheory.average_eq]
  refine MeasureTheory.integral_nonneg_of_ae ?_ |> smul_nonneg (by positivity)
  refine Filter.Eventually.of_forall fun v => ?_
  unfold GT.ptN2
  positivity

theorem le_firstMinimum_of_period_lower_bound (Y : GT ι) (hι : Fintype.card ι ≠ 0) {lam : ℝ}
    (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖) : lam ≤ Y.la1 := by
  refine le_csInf ⟨‖Y.b ⟨0, by omega⟩‖, Y.b ⟨0, by omega⟩,
    Submodule.subset_span ⟨_, rfl⟩, Y.b.ne_zero _, rfl⟩ ?_
  rintro t ⟨x, hx, hx0, rfl⟩
  exact hmin x hx hx0

theorem pointwiseNormSq_le_l2_of_firstMinimum (hsup : GSupStatement) (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec 1)
    {lam : ℝ} (hlam : 0 < lam) (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖)
    (v : EuclideanSpace ℂ ι) :
    Y.ptN2 1 F v ≤ (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) /
      (Real.sqrt Real.pi * lam)) ^ Fintype.card ι) ^ 2 * Y.l2 1 F := by
  refine (hsup ι Y 1 le_rfl F hF v).trans (mul_le_mul_of_nonneg_right ?_ (l2NormSq_nonneg_gaussianTorus Y 1 F))
  rw [mul_pow, Real.sq_sqrt (by norm_num), ← pow_mul, mul_comm (Fintype.card ι) 2]
  simp only [Nat.cast_one, one_pow, mul_one, one_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  by_cases hι : Fintype.card ι = 0
  · simp [hι]
  have h1 := le_firstMinimum_of_period_lower_bound Y hι hmin
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h2 : 0 < Y.la1 := hlam.trans_le h1
  gcongr

end General

section Columns

open TensorLat

variable {E : Type} [Field E] [NumberField E]

theorem col_mem_Sec (X : PT E) {q : ℕ} {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec q 1) :
    (fun z => s fun _ => z) ∈ (gtOf X q).Sec q := by
  refine ⟨hs.1.comp (differentiable_pi.2 fun _ => differentiable_id), fun γ hγ v => ?_⟩
  have e : (fun _ : Fin 1 => v + γ) = (fun _ => v) + (fun _ => γ) := by funext j; simp
  simp only [e]
  rw [hs.2 (fun _ => γ) (fun _ => hγ) (fun _ => v)]
  simp [HC, gtOf]

theorem oneColumn_pointwiseNorm_eq_torus (X : PT E) (q : ℕ) (s : (Fin 1 → Vsp X.dim) → ℂ) (x : Vsp X.dim) :
    (gtOf X q).ptN2 q (fun z => s fun _ => z) x = X.ptN2 q s fun _ => x := by
  simp [GT.ptN2, PT.ptN2, HC, jof_Hf_self_re]

theorem oneColumn_l2Norm_eq_torus (X : PT E) (q : ℕ) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    (gtOf X q).l2 q (fun z => s fun _ => z) = X.l2 q s := by
  rw [l2_norm_fundamental_domain, GT.l2]
  simp only [oneColumn_pointwiseNorm_eq_torus]
  rfl

theorem l2_pos_of_mem_sec_of_ne_zero (X : PT E) {q : ℕ} (hq : 1 ≤ q) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec q 1)
    (hne : s ≠ 0) : 0 < X.l2 q s := by
  refine lt_of_le_of_ne ?_ fun h => hne (eq_zero_of_l2_eq_zero X packingCount hq hs h.symm)
  rw [← oneColumn_l2Norm_eq_torus]
  exact l2NormSq_nonneg_gaussianTorus _ _ _

end Columns

end ThetaBound

open Classical in

theorem theta_value_bound (hsup : GSupStatement) {ι : Type} [Fintype ι] (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
    (hU : ∀ (q : ℕ) a F v, U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
    (Y : GT ι) (F : EuclideanSpace ℂ ι → ℂ) (hF : F ∈ Y.Sec 1) (lam : ℝ) (hlam : 0 < lam) (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖)
    {κ : Type} (s : Finset κ) (c : κ → ℂ) (hc : ∀ j ∈ s, ‖c j‖ ≤ 1) (y : κ → EuclideanSpace ℂ ι)
    (P : MvPolynomial ι ℂ) (a : ℕ) (hP : P.IsHomogeneous a) :
    ‖∑ j ∈ s, c j * polyDeriv P (fun i => EuclideanSpace.single i 1) (U 1 (y j) F) 0‖ ≤
      s.card * (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) *
        (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) / (Real.sqrt Real.pi * lam)) ^ Fintype.card ι) * Real.sqrt (Y.l2 1 F) := by
  set C : ℝ := Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) /
    (Real.sqrt Real.pi * lam)) ^ Fintype.card ι with hC
  have hC0 : 0 ≤ C := by positivity
  have key : ∀ j ∈ s,
      ‖c j * polyDeriv P (fun i => EuclideanSpace.single i 1) (U 1 (y j) F) 0‖ ≤
        (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) * C *
          Real.sqrt (Y.l2 1 F) := by
    intro j hj
    have h := translate_jet_bound U hU 1 le_rfl F hF.1 (C ^ 2 * Y.l2 1 F)
      (ThetaBound.pointwiseNormSq_le_l2_of_firstMinimum hsup Y hF hlam hmin) P a hP (y j)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC0, Nat.cast_one, one_mul] at h
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hc j hj)).trans (h.trans_eq ?_)
    ring
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ key).trans_eq ?_)
  rw [nsmul_eq_mul]
  ring

end GlobalTheory
