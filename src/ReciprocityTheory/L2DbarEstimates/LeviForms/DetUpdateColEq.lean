import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart

namespace ReciprocityTheory.L2DbarEstimates.I

namespace MongeAmpereIntegrability

open MeasureTheory Filter Topology Set
open scoped ContDiff

noncomputable section

variable {n : ℕ}

theorem cdo_wd {Ω : Set (V n)} (hΩ : IsOpen Ω) {g : V n → ℂ} (hg : ContDiffOn ℝ ∞ g Ω)
    (j : Fin n) : ContDiffOn ℝ ∞ (wd n j g) Ω ∧ ContDiffOn ℝ ∞ (wdb n j g) Ω := by
  have hF : ∀ v : V n, ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y v) Ω := fun v =>
    ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 hg).2.clm_apply contDiffOn_const
  constructor
  · unfold wd
    exact ((hF _).sub (contDiffOn_const.mul (hF _))).div_const 2
  · unfold wdb
    exact ((hF _).add (contDiffOn_const.mul (hF _))).div_const 2

theorem cdo_ofReal {Ω : Set (V n)} {p : V n → ℝ} (hp : ContDiffOn ℝ ∞ p Ω) :
    ContDiffOn ℝ ∞ (fun w => (p w : ℂ)) Ω := Complex.ofRealCLM.contDiff.comp_contDiffOn hp

private theorem lin_lemma' {g₁ g₂ : V n → ℂ} {y : V n} (h₁ : DifferentiableAt ℝ g₁ y)
    (h₂ : DifferentiableAt ℝ g₂ y) (c : ℂ) (j : Fin n) :
    wd n j (fun w => g₁ w + c * g₂ w) y = wd n j g₁ y + c * wd n j g₂ y ∧
      wdb n j (fun w => g₁ w + c * g₂ w) y = wdb n j g₁ y + c * wdb n j g₂ y := by
  have hF : fderiv ℝ (fun w => g₁ w + c * g₂ w) y = fderiv ℝ g₁ y + c • fderiv ℝ g₂ y := by
    have H : HasFDerivAt (fun w => g₁ w + c * g₂ w) (fderiv ℝ g₁ y + c • fderiv ℝ g₂ y) y :=
      h₁.hasFDerivAt.add (h₂.hasFDerivAt.const_mul c)
    exact H.fderiv
  constructor <;>
    simp only [wd, wdb, hF, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul] <;> ring

theorem cHess_add_smul {Ω : Set (V n)} (hΩ : IsOpen Ω) {p q : V n → ℝ}
    (hp : ContDiffOn ℝ ∞ p Ω) (hq : ContDiffOn ℝ ∞ q Ω) (t : ℝ) {y : V n} (hy : y ∈ Ω) :
    cHess n (fun w => ((p w + t * q w : ℝ) : ℂ)) y =
      cHess n (fun w => (p w : ℂ)) y + (t : ℂ) • cHess n (fun w => (q w : ℂ)) y := by
  ext j k
  simp only [cHess, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hP := cdo_ofReal hp
  have hQ := cdo_ofReal hq
  have dP : ∀ v ∈ Ω, DifferentiableAt ℝ (fun w => (p w : ℂ)) v := fun v hv =>
    (hP.contDiffAt (hΩ.mem_nhds hv)).differentiableAt (by simp)
  have dQ : ∀ v ∈ Ω, DifferentiableAt ℝ (fun w => (q w : ℂ)) v := fun v hv =>
    (hQ.contDiffAt (hΩ.mem_nhds hv)).differentiableAt (by simp)
  have hfun : (fun w => ((p w + t * q w : ℝ) : ℂ)) = fun w => (p w : ℂ) + (t : ℂ) * (q w : ℂ) := by
    funext w; push_cast; ring
  rw [hfun]
  have hev : wdb n k (fun w => (p w : ℂ) + (t : ℂ) * (q w : ℂ)) =ᶠ[𝓝 y]
      fun v => wdb n k (fun w => (p w : ℂ)) v + (t : ℂ) * wdb n k (fun w => (q w : ℂ)) v := by
    filter_upwards [hΩ.mem_nhds hy] with v hv
    exact (lin_lemma' (dP v hv) (dQ v hv) _ k).2
  have e1 : wd n j (wdb n k (fun w => (p w : ℂ) + (t : ℂ) * (q w : ℂ))) y =
      wd n j (fun v => wdb n k (fun w => (p w : ℂ)) v + (t : ℂ) * wdb n k (fun w => (q w : ℂ)) v) y := by
    simp only [wd, hev.fderiv_eq]
  rw [e1]
  have dP' : DifferentiableAt ℝ (wdb n k (fun w => (p w : ℂ))) y :=
    (((cdo_wd hΩ hP k).2).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have dQ' : DifferentiableAt ℝ (wdb n k (fun w => (q w : ℂ))) y :=
    (((cdo_wd hΩ hQ k).2).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  exact (lin_lemma' dP' dQ' _ j).1

end

end MongeAmpereIntegrability

end ReciprocityTheory.L2DbarEstimates.I
