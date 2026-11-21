import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCompactDualHaar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMatExp
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt

noncomputable section

namespace GlobalTheory.SUVol

open MeasureTheory Filter Topology Matrix Metric Set
open scoped ENNReal NNReal

theorem exists_density_of_immersion (V M G : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (lam : Measure V) [lam.IsAddHaarMeasure] (μ : Measure G) [μ.IsHaarMeasure]
    (e : V → G) (m : G → M) (j : V →L[ℝ] M) (hj : Function.Injective j) (L : G → M →L[ℝ] M) (he : Continuous e)
    (h0 : e 0 = 1) (hd : HasStrictFDerivAt (fun x => m (e x)) j 0)
    (hL : ContinuousAt L 1) (hL1 : L 1 = ContinuousLinearMap.id ℝ M)
    (hm : ∀ g h, m (g * h) = L g (m h)) (hn : ∀ r : ℝ, 0 < r → e '' ball 0 r ∈ 𝓝 (1 : G)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      Tendsto (fun r : ℝ => μ (e '' ball 0 r) / lam (ball 0 r)) (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨p₀, hp₀⟩ := (j : V →ₗ[ℝ] M).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hj)
  let p : M →L[ℝ] V := LinearMap.toContinuousLinearMap p₀
  have hp : ∀ v, p (j v) = v := fun v => LinearMap.congr_fun hp₀ v
  let E : M →L[ℝ] V × M := p.prod (ContinuousLinearMap.id ℝ M - j.comp p)
  let D : V × M →L[ℝ] M := j.coprod (ContinuousLinearMap.id ℝ M)
  have hDE : ∀ x, D (E x) = x := fun x => by simp [D, E]
  let J : V →ₗᵢ[ℝ] V × M := ⟨LinearMap.inl ℝ V M, fun v => by simp⟩
  have hJ : E.comp j = J.toContinuousLinearMap := by
    ext v <;> simp [E, J, hp]
  refine GlobalTheory.CompactDualExists.exists_density_of_chart V (V × M) G lam μ e (fun g => E (m g)) J
    (fun g => ContinuousLinearMap.id ℝ _ + E.comp ((L g - ContinuousLinearMap.id ℝ M).comp D)) he h0
    (hJ ▸ E.hasStrictFDerivAt.comp 0 hd) ?_ (by simp [hL1]) (fun g h => ?_) hn
  · exact continuousAt_const.add (continuousAt_const.clm_comp ((hL.sub continuousAt_const).clm_comp
      continuousAt_const))
  · simp [hm, hDE]

section OneMatrix

variable {r : ℕ}

theorem det_exp (X : Matrix (Fin r) (Fin r) ℂ) : (NormedSpace.exp X).det = Complex.exp X.trace := by
  have hder : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)).det) X.trace 0 := by
    have h1 : ∀ a b, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) a b) (X a b) 0 := by
      intro a b
      open scoped Matrix.Norms.Operator in
      have h2 := ((Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
        (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
      rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
      exact h2
    have h3 := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t : ℝ => NormedSpace.exp (t • X)) X 0 h1
    simpa only [zero_smul, NormedSpace.exp_zero, Matrix.adjugate_one, Matrix.one_mul] using h3
  have hadd : ∀ s t : ℝ,
      NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X) := by
    intro s t
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)
  set f : ℝ → ℂ := fun t => (NormedSpace.exp (t • X)).det with hf
  have hd : ∀ t, HasDerivAt f (f t * X.trace) t := by
    intro t
    have h0 : HasDerivAt f X.trace (t - t) := by
      rw [sub_self]; exact hder
    have h1 := (h0.comp_sub_const t t).const_mul (f t)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [hf]
    rw [← Matrix.det_mul, ← hadd, add_sub_cancel]
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f s * Complex.exp (-(s * X.trace))) 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * X.trace)) (-X.trace) t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const X.trace).fun_neg
    exact ((hd t).fun_mul h1.cexp).congr_deriv (by ring)
  have h2 := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, NormedSpace.exp_zero, Matrix.det_one, Complex.ofReal_one, one_mul,
    Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, Complex.exp_neg] at h2
  exact (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).1 h2

theorem map_conj_eq (A : Matrix (Fin r) (Fin r) ℂ) : A.map (starRingEnd ℂ) = Aᴴᵀ := rfl

theorem exp_map_conj (A : Matrix (Fin r) (Fin r) ℂ) :
    NormedSpace.exp (A.map (starRingEnd ℂ)) = (NormedSpace.exp A).map (starRingEnd ℂ) := by
  rw [map_conj_eq, map_conj_eq, Matrix.exp_transpose, Matrix.exp_conjTranspose]

def twist (H X : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  (H * (-X).map (starRingEnd ℂ) * H⁻¹)ᵀ

theorem continuous_twist (H : Matrix (Fin r) (Fin r) ℂ) : Continuous (twist H) :=
  ((continuous_const.matrix_mul (continuous_neg.matrix_map Complex.continuous_conj)).matrix_mul
    continuous_const).matrix_transpose

variable {H : Matrix (Fin r) (Fin r) ℂ}

theorem twist_transpose_mul (hH : H.det ≠ 0) (X : Matrix (Fin r) (Fin r) ℂ) :
    (twist H X)ᵀ * H = -(H * X.map (starRingEnd ℂ)) := by
  rw [twist, transpose_transpose, Matrix.nonsing_inv_mul_cancel_right _ _ hH.isUnit,
    Matrix.map_neg _ (map_neg _), Matrix.mul_neg]

theorem twist_eq_iff (hH : H.det ≠ 0) (X : Matrix (Fin r) (Fin r) ℂ) :
    twist H X = X ↔ Xᵀ * H + H * X.map (starRingEnd ℂ) = 0 := by
  constructor
  · intro h
    have := twist_transpose_mul hH X
    rw [h] at this
    rw [this, neg_add_cancel]
  · intro h
    rw [twist, Matrix.map_neg _ (map_neg _), Matrix.mul_neg, ← eq_neg_of_add_eq_zero_left h,
      Matrix.mul_nonsing_inv_cancel_right _ _ hH.isUnit, transpose_transpose]

theorem exp_twist (hH : H.det ≠ 0) (X : Matrix (Fin r) (Fin r) ℂ) :
    (NormedSpace.exp (twist H X))ᵀ * H * (NormedSpace.exp X).map (starRingEnd ℂ) = H := by
  rw [twist, Matrix.exp_transpose, transpose_transpose,
    Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det _).2 hH.isUnit),
    Matrix.nonsing_inv_mul_cancel_right _ _ hH.isUnit, exp_map_conj, Matrix.mul_assoc, ← Matrix.map_mul,
    GlobalTheory.UpqExpChart.exp_neg_mul_exp]
  simp

theorem exp_twist_eq (hH : H.det ≠ 0) {X : Matrix (Fin r) (Fin r) ℂ}
    (h : (NormedSpace.exp X)ᵀ * H * (NormedSpace.exp X).map (starRingEnd ℂ) = H) :
    NormedSpace.exp (twist H X) = NormedSpace.exp X := by
  have h1 := (exp_twist hH X).trans h.symm
  have h2 := congrArg (fun A => A * (NormedSpace.exp (-X)).map (starRingEnd ℂ) * H⁻¹) h1
  simp only [Matrix.mul_assoc _ ((NormedSpace.exp X).map (starRingEnd ℂ)), ← Matrix.map_mul,
    GlobalTheory.UpqExpChart.exp_mul_exp_neg, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_right _ _ hH.isUnit] at h2
  exact transpose_injective h2

end OneMatrix

variable {ι : Type} {r : ℕ} {H : ι → Matrix (Fin r) (Fin r) ℂ}

end GlobalTheory.SUVol
