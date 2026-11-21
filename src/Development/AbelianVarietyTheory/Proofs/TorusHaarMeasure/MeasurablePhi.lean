import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralFundSetInterLe
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralBallLtTopOfLocalInverse
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsOpenSaturation
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OfRealRpowNegLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivInFFPf

open Filter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem muF_lt_top (hM : MeasInvStatement (E := E)) (hfin : FinMu X) {x0 : Frame X.Ψ r}
    (ho : IsOrth X x0) {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) : muF X x0 FF < ⊤ := by
  classical
  obtain ⟨x1, ho1, F1, hF1, hlt⟩ := hfin
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hle := GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 x1 ho ho1 FF hF (fun _ => 1)
    measurable_const (fun _ _ _ _ _ _ => rfl) F1 hF1.1 hF1.2.1
  simp only [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hle
  let S : Set (Frame X.Ψ r) := ⋃ γ : X.Γ, (fun x => lact (γ.1)⁻¹ x) ⁻¹' GlobalTheory.Unfold.satFrames X x1 F1
  have hS : MeasurableSet S := MeasurableSet.iUnion fun γ =>
    (GlobalTheory.Unfold.continuous_lact X _).measurable (GlobalTheory.Unfold.measurableSet_satFrames X ho1 hF1.1 hF1.2.1)
  have hSiff : ∀ x, x ∈ S ↔ ∃ y ∈ F1, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b) := by
    intro x
    simp only [S, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨γ, y, hy, b, hb, h⟩
      refine ⟨y, hy, γ.1, γ.2, b, hb, ?_⟩
      rw [← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]
    · rintro ⟨y, hy, γ, hγ, b, hb, rfl⟩
      exact ⟨⟨γ, hγ⟩, y, hy, b, hb, FundSetPf.lact_inv _ _⟩
  have hψ : Measurable (Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞)) := measurable_one.indicator hS.compl
  have hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul x b) = Sᶜ.indicator 1 x := by
    intro x _ b hb
    have : rmul x b ∈ S ↔ x ∈ S := by
      simp only [S, Set.mem_iUnion, Set.mem_preimage, FundSetPf.lact_rmul,
        GlobalTheory.Unfold.rmul_mem_satFrames_iff X x1 F1 _ hb]
    simp only [Set.indicator, Set.mem_compl_iff, this, Pi.one_apply]
  have h0 : ∫⁻ z, Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) ∂muF X x0 = 0 := by
    rw [hM r X x0 x1 ho ho1 _ hψ hB]
    refine (lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero
    filter_upwards [hF1.2.2.2] with z hz
    exact Set.indicator_of_notMem (Set.notMem_compl_iff.2 ((hSiff _).2 hz)) _
  have hae := (lintegral_eq_zero_iff (hψ.comp (FundSetPf.cont_cpt X x0).measurable)).1 h0
  refine lt_of_le_of_lt (measure_mono_ae ?_) (hle.trans_lt hlt)
  filter_upwards [hae] with z hz hzF
  refine ⟨hzF, (hSiff _).1 ?_⟩
  by_contra hn
  have : Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) = 0 := hz
  rw [Set.indicator_of_mem (show _ ∈ Sᶜ from hn)] at this
  exact one_ne_zero this

variable (Xa : ArchInM X) (Fl : FlatM X Xa)

theorem ae_exists_ne {x0 : Frame X.Ψ r} (ho : IsOrth X x0) :
    ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 → ∃ k, Fl.s k (cpt X x0 z) ≠ 0 := by
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hn := Xa.n_ge
  have : Nonempty (Fin (nd X)) := ⟨⟨0, by omega⟩⟩
  have hc : (⋃ j : Fin Fl.δ, ⋃ γ : GL (Fin r) E,
      {z | ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (Fl.xs j) b)}).Countable := by
    refine Set.countable_iUnion fun j => Set.countable_iUnion fun γ => Set.Subsingleton.countable ?_
    rintro z ⟨b, hb, h⟩ z' ⟨b', hb', h'⟩
    refine FundSetPf.cpt_uniq X ho (ExtFPf.invF_mem X hb) (ExtFPf.invF_mem X hb') ?_
    rw [h, h', FundSetPf.lact_rmul, FundSetPf.lact_rmul, ExtFPf.rmul_assoc, ExtFPf.rmul_assoc,
      ExtFPf.rmul_invF X hb, ExtFPf.rmul_invF X hb']
  have hac : muF X x0 ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  filter_upwards [hac.ae_le (hc.ae_notMem volume)] with z hz hzO
  by_contra hs
  push Not at hs
  obtain ⟨j, γ, -, b, hb, h⟩ := (Fl.S_eq _ hzO).1 hs
  exact hz (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨γ, b, hb, h⟩⟩)

theorem pnorm_contOn {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) :
    ContinuousOn (X.pnorm la P) X.dom :=
  hP.1.continuousOn.norm.mul (ExtFPf.nfac_contOn X la)

theorem measurable_cut {f : Frame X.Ψ r → ℝ} (hf : ContinuousOn f X.dom) :
    Measurable (X.dom.indicator f) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise hf continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet

theorem sum_pnorm_pos {N : ℕ} {la : Wt X.Ψ r} {P : Fin N → Frame X.Ψ r → ℂ} {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (h : ∃ k, P k x ≠ 0) : 0 < ∑ k, X.pnorm la (P k) x ^ 2 := by
  simp only [pnorm_sq_eq_exp hx, ← Finset.mul_sum]
  exact mul_pos (Real.exp_pos _) (sum_normSq_pos h)

theorem real_bound {e F G w s K C : ℝ} {a b : ℂ} {n : ℕ} (hn : 1 ≤ n) (he : 0 ≤ e) (hF : F = e * ‖a‖ ^ 2)
    (hG : G = e * ‖b‖ ^ 2) (hw : 0 < w) (hs : 0 ≤ s) (hK : w ≤ K * s) (hC : G ≤ C * w ^ n) :
    e * ‖a - b‖ ^ 2 * w ^ (-(1 / 2 : ℝ)) * s ^ (-((n : ℝ) - 1 / 2)) ≤
      2 * |K| ^ ((n : ℝ) - 1 / 2) * (F * w ^ (-(n : ℝ))) + 2 * |K| ^ ((n : ℝ) - 1 / 2) * C := by
  have hn' : 0 ≤ (n : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hKs : 0 < K * s := hw.trans_le hK
  have hs' : 0 < s := lt_of_le_of_ne hs (by rintro rfl; simp at hKs)
  have hK0 : 0 < K := (mul_pos_iff_of_pos_right hs').1 hKs
  rw [abs_of_pos hK0]
  have h1 : s ^ (-((n : ℝ) - 1 / 2)) ≤ K ^ ((n : ℝ) - 1 / 2) * w ^ (-((n : ℝ) - 1 / 2)) := by
    have : (K * s) ^ (-((n : ℝ) - 1 / 2)) ≤ w ^ (-((n : ℝ) - 1 / 2)) :=
      Real.rpow_le_rpow_of_nonpos hw hK (by linarith)
    rw [Real.mul_rpow hK0.le hs, Real.rpow_neg hK0.le,
      inv_mul_le_iff₀ (Real.rpow_pos_of_pos hK0 _)] at this
    exact this
  have h2 : w ^ (-(1 / 2 : ℝ)) * w ^ (-((n : ℝ) - 1 / 2)) = w ^ (-(n : ℝ)) := by
    rw [← Real.rpow_add hw]; congr 1; ring
  have h3 : e * ‖a - b‖ ^ 2 ≤ 2 * F + 2 * G := by
    have h4 : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
      nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    rw [hF, hG]
    nlinarith [mul_le_mul_of_nonneg_left h4 he]
  have h5 : G * w ^ (-(n : ℝ)) ≤ C := by
    rw [Real.rpow_neg hw.le, Real.rpow_natCast, mul_inv_le_iff₀ (pow_pos hw n)]
    exact hC
  have hKp := Real.rpow_pos_of_pos hK0 ((n : ℝ) - 1 / 2)
  calc e * ‖a - b‖ ^ 2 * w ^ (-(1 / 2 : ℝ)) * s ^ (-((n : ℝ) - 1 / 2))
      ≤ (2 * F + 2 * G) * w ^ (-(1 / 2 : ℝ)) * (K ^ ((n : ℝ) - 1 / 2) * w ^ (-((n : ℝ) - 1 / 2))) := by
        have : 0 ≤ 2 * F + 2 * G := le_trans (by positivity) h3
        gcongr
    _ = 2 * K ^ ((n : ℝ) - 1 / 2) * (F * w ^ (-(n : ℝ))) +
          2 * K ^ ((n : ℝ) - 1 / 2) * (G * w ^ (-(n : ℝ))) := by rw [← h2]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.Up.DivInFFPf
