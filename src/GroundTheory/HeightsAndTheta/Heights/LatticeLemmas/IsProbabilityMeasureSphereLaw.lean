import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogGaussNormSupportFinite
import GroundTheory.HeightsAndTheta.Heights.HermitianDual
import GroundTheory.HeightsAndTheta.Heights.ArithDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField MeasureTheory ProbabilityTheory TensorProduct ComplexAt

noncomputable section

section GaussNorms

def normAbv (L : Type*) [NormedField L] : AbsoluteValue L ℝ where
  toFun := norm
  map_mul' := norm_mul
  nonneg' := norm_nonneg
  eq_zero' _ := norm_eq_zero
  add_le' := norm_add_le

variable {L : Type*} [Field L]

end GaussNorms

section Sphere

variable {n : ℕ}

def sphereBall (h : HermNorm n) (k : ℕ) : Set (Fin k × Fin n → ℂ) :=
  {u | ∀ i, h.norm (fun j ↦ u (i, j)) < 1}

def sphereNormalize (h : HermNorm n) (k : ℕ) (u : Fin k × Fin n → ℂ) : Fin k × Fin n → ℂ :=
  fun ij ↦ ((h.norm fun j ↦ u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij

theorem sphereMean_eq (h : HermNorm n) (k : ℕ) (g : (Fin k × Fin n → ℂ) → ℝ) :
    sphereMean h k g = ⨍ u in sphereBall h k, g (sphereNormalize h k u) := rfl

def sphereLaw (N : ℕ) : Measure (Fin N → ℂ) :=
  (volume[|sphereBall (HermNorm.std N) 1]).map
    fun u j ↦ sphereNormalize (HermNorm.std N) 1 u (0, j)

end Sphere

section HeightsOfPoints

def intToField (F K : Type*) [Field F] [Field K] [Algebra F K] : 𝓞 F →+* K :=
  (algebraMap F K).comp (algebraMap (𝓞 F) F)

variable {F : Type*} [Field F] [NumberField F] {W : Type*} [AddCommGroup W] [Module (𝓞 F) W]

abbrev DualVec (F : Type*) [Field F] (W : Type*) [AddCommGroup W] [Module (𝓞 F) W]
    (K : Type*) [Field K] [Algebra F K] : Type _ :=
  W →ₛₗ[intToField F K] K

variable {K : Type*} [Field K] [NumberField K] [Algebra F K]

variable [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W]

end HeightsOfPoints

section Inhabitants

theorem HermNorm.std_norm_eq {n : ℕ} (v : Fin n → ℂ) :
    (HermNorm.std n).norm v = √(∑ i, ‖v i‖ ^ 2) := by
  simp [HermNorm.norm, HermNorm.std]

theorem isOpen_sphereBall_std (N : ℕ) : IsOpen (sphereBall (HermNorm.std N) 1) := by
  have : sphereBall (HermNorm.std N) 1 = ⋂ i : Fin 1, {u | (HermNorm.std N).norm (fun j ↦ u (i, j)) < 1} := by
    ext u; simp [sphereBall]
  rw [this]
  refine isOpen_iInter_of_finite fun i ↦ isOpen_lt ?_ continuous_const
  simp only [HermNorm.std_norm_eq]
  fun_prop

theorem sphereBall_std_subset (N : ℕ) : sphereBall (HermNorm.std N) 1 ⊆ Metric.closedBall 0 1 := by
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro ij
  have h := hu ij.1
  rw [HermNorm.std_norm_eq] at h
  have hle : ‖u ij‖ ≤ √(∑ j, ‖u (ij.1, j)‖ ^ 2) := by
    rw [Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ by positivity)]
    have := Finset.single_le_sum (f := fun j ↦ ‖u (ij.1, j)‖ ^ 2) (fun _ _ ↦ by positivity)
      (Finset.mem_univ ij.2)
    simpa using this
  linarith

instance isProbabilityMeasure_sphereLaw (N : ℕ) : IsProbabilityMeasure (sphereLaw N) := by
  have h0 : volume (sphereBall (HermNorm.std N) 1) ≠ 0 := by
    refine ((isOpen_sphereBall_std N).measure_pos volume ⟨0, ?_⟩).ne'
    simp [sphereBall, HermNorm.std_norm_eq]
  have htop : volume (sphereBall (HermNorm.std N) 1) ≠ ⊤ :=
    ((measure_mono (sphereBall_std_subset N)).trans_lt
      (isCompact_closedBall 0 1).measure_lt_top).ne
  have := cond_isProbabilityMeasure_of_finite h0 htop
  unfold sphereLaw
  refine Measure.isProbabilityMeasure_map (Measurable.aemeasurable ?_)
  unfold sphereNormalize
  simp only [HermNorm.std_norm_eq]
  fun_prop

def ratPointVec : DualVec ℚ (Fin 2 → 𝓞 ℚ) ℚ where
  toFun x := (x 0 : ℚ) + 2 * (x 1 : ℚ)
  map_add' x y := by simp only [Pi.add_apply, map_add]; ring
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, intToField, RingHom.comp_apply,
      map_mul, Algebra.algebraMap_self, RingHom.id_apply]
    ring

theorem ratPointVec_apply (x : Fin 2 → 𝓞 ℚ) : ratPointVec x = (x 0 : ℚ) + 2 * (x 1 : ℚ) := rfl

end Inhabitants

end

end GroundTheory.Heights₂.Heights
