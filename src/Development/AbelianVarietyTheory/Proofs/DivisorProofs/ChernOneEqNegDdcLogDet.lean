import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm

open Matrix Complex ComplexConjugate Filter Topology

noncomputable section

namespace GlobalTheory.HermFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}

theorem del_finsetProd {ι : Type*} [DecidableEq ι] (t : Finset ι) {f : ι → E → ℂ} {z : E}
    (h : ∀ i ∈ t, DifferentiableAt ℝ (f i) z) (ξ : E) :
    del (fun x => ∏ i ∈ t, f i x) z ξ = ∑ i ∈ t, (∏ j ∈ t.erase i, f j z) * del (f i) z ξ := by
  have h1 := (HasFDerivAt.finsetProd (u := t) (g := f) (fun i hi => (h i hi).hasFDerivAt)).fderiv
  simp only [del_apply, h1, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

section Det

variable [Fintype n] [DecidableEq n] {H : E → Matrix n n ℂ} {z : E}

theorem trace_adjugate_mul_eq_sum (A B : Matrix n n ℂ) :
    (A.adjugate * B).trace = ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℂ) *
      ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) * B (σ i) i := by
  have h1 : ∀ i, (A.adjugate * B) i i = (A.updateCol i (fun k => B k i)).det := by
    intro i
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp only [Matrix.trace, Matrix.diag, h1, det_apply']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [updateCol_apply]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [if_neg (Finset.ne_of_mem_erase hj)]

theorem del_det (h : MContDiffAt 1 H z) (ξ : E) :
    del (fun x => (H x).det) z ξ = ((H z).adjugate * mdel H z ξ).trace := by
  have hp : ∀ σ : Equiv.Perm n, DifferentiableAt ℝ (fun x => ∏ i, H x (σ i) i) z := fun σ =>
    (contDiffAt_prod fun c _ => h (σ c) c).differentiableAt one_ne_zero
  simp only [det_apply']
  rw [del_sum fun σ _ => (differentiableAt_const _).fun_mul (hp σ), trace_adjugate_mul_eq_sum,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [del_mul (differentiableAt_const _) (hp σ),
    del_finsetProd _ (f := fun i x => H x (σ i) i) fun i _ => h.diff _ _]
  simp

theorem trace_conn (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det) (ξ : E) :
    (conn H z ξ).trace = (H z).det⁻¹ * del (fun x => (H x).det) z ξ := by
  have _ := hu
  rw [del_det h, conn, ← transpose_nonsing_inv, ← transpose_mul, trace_transpose, trace_mul_comm,
    Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, trace_smul, smul_eq_mul]

theorem trace_curv_eq_neg_dbar (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : E) :
    (curv H z ξ η).trace = -dbar (fun x => (conn H x ξ).trace) z η := by
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := h.conn hu (by norm_num) ξ
  simp only [curv, trace, diag_apply, Matrix.neg_apply, mdbar_apply, Finset.sum_neg_distrib]
  rw [dbar_sum fun a _ => hc.diff a a, ContinuousLinearMap.sum_apply]

theorem trace_curv_eq_curv_det (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : E) :
    (curv H z ξ η).trace =
      curv (fun x => (of fun _ _ => (H x).det : Matrix Unit Unit ℂ)) z ξ η () () := by
  have he : (fun x => (conn H x ξ).trace) =ᶠ[𝓝 z]
      fun x => conn (fun x => (of fun _ _ => (H x).det : Matrix Unit Unit ℂ)) x ξ () () := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu] with x h1 h2
    rw [trace_conn (h1.of_le one_le_two) h2]
    simp [conn, Matrix.mul_apply]
  rw [trace_curv_eq_neg_dbar h hu, dbar_congr he]
  rfl

theorem ofReal_re_det {M : Matrix n n ℂ} (hM : M.IsHermitian) : (M.det.re : ℂ) = M.det := by
  refine conj_eq_iff_re.1 ?_
  rw [← star_def, ← det_conjTranspose, hM.eq]

theorem trace_curv (h : MContDiffAt 2 H z) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu : IsUnit (H z).det) (ξ η : E) :
    (curv H z ξ η).trace = -leviForm (fun x => Real.log (H x).det.re) z ξ η := by
  rw [trace_curv_eq_curv_det h hu]
  refine curv_line (f := fun x => (H x).det.re) (reCLM.contDiff.contDiffAt.comp z h.det) ?_
    (hh.mono fun x hx => (ofReal_re_det hx).symm) ξ η () ()
  intro h0
  apply hu.ne_zero
  rw [← ofReal_re_det hh.self_of_nhds, ofReal_eq_zero]
  exact h0

theorem chernOne_eq_neg_ddc_log_det (h : MContDiffAt 2 H z)
    (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian) (hu : IsUnit (H z).det) (ξ η : E) :
    chernOne H z ξ η = -ddc (fun x => Real.log (H x).det.re) z ξ η := by
  rw [chernOne, trace_curv h hh hu, ddc, mul_neg]

end Det

end GlobalTheory.HermFrame
