import Mathlib
import GroundTheory.AutomorphicForms.KernelTrace

namespace GroundTheory.Automorphic

open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal

noncomputable section

section Uniform

variable {X : Type*} [UniformSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

theorem continuous_integral_mul_of_uniformSpace (a b : C(X × X, ℂ)) :
    Continuous fun z : X × X => ∫ y, a (z.1, y) * b (y, z.2) ∂μ := by
  refine UniformContinuous.continuous ?_
  refine (Metric.uniformity_basis_dist.tendsto_right_iff).2 fun ε hε => ?_
  set A := ‖a‖
  set B := ‖b‖
  set M := μ.real univ
  set δ : ℝ := ε / ((A + B) * M + 1)
  have hδ : 0 < δ := by positivity
  obtain ⟨u₁, hu₁, v₁, hv₁, h₁⟩ := entourageProd_subset
    (CompactSpace.uniformContinuous_of_continuous a.continuous (Metric.dist_mem_uniformity hδ))
  obtain ⟨u₂, hu₂, v₂, hv₂, h₂⟩ := entourageProd_subset
    (CompactSpace.uniformContinuous_of_continuous b.continuous (Metric.dist_mem_uniformity hδ))
  filter_upwards [entourageProd_mem_uniformity hu₁ hv₂] with w hw
  obtain ⟨⟨x, z⟩, ⟨x', z'⟩⟩ := w
  obtain ⟨hx, hz⟩ := hw
  change dist (∫ y, a (x, y) * b (y, z) ∂μ) (∫ y, a (x', y) * b (y, z') ∂μ) < ε
  have hrowa : ∀ x, Continuous fun y => a (x, y) := fun x =>
    a.continuous.comp (continuous_const.prodMk continuous_id)
  have hcolb : ∀ z, Continuous fun y => b (y, z) := fun z =>
    b.continuous.comp (continuous_id.prodMk continuous_const)
  have hint : ∀ x z, Integrable (fun y => a (x, y) * b (y, z)) μ := fun x z =>
    integrable_of_continuous_compact ((hrowa x).mul (hcolb z)) μ
  rw [dist_eq_norm, ← integral_sub (hint x z) (hint x' z')]
  have hpt : ∀ y, ‖a (x, y) * b (y, z) - a (x', y) * b (y, z')‖ ≤ δ * B + A * δ := by
    intro y
    have ha : ‖a (x, y) - a (x', y)‖ < δ := by
      rw [← dist_eq_norm]
      exact h₁ (show ((x, y), (x', y)) ∈ entourageProd u₁ v₁ from ⟨hx, refl_mem_uniformity hv₁⟩)
    have hb : ‖b (y, z) - b (y, z')‖ < δ := by
      rw [← dist_eq_norm]
      exact h₂ (show ((y, z), (y, z')) ∈ entourageProd u₂ v₂ from ⟨refl_mem_uniformity hu₂, hz⟩)
    have e : a (x, y) * b (y, z) - a (x', y) * b (y, z') =
        (a (x, y) - a (x', y)) * b (y, z) + a (x', y) * (b (y, z) - b (y, z')) := by ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul ha.le (b.norm_coe_le_norm _) (norm_nonneg _) hδ.le
    · rw [norm_mul]
      exact mul_le_mul (a.norm_coe_le_norm _) hb.le (norm_nonneg _) (norm_nonneg _)
  refine (norm_integral_le_of_norm_le_const (ae_of_all _ hpt)).trans_lt ?_
  have hM : 0 ≤ M := measureReal_nonneg
  have hAB : 0 ≤ A + B := by positivity
  have e : (δ * B + A * δ) * M = ε * ((A + B) * M / ((A + B) * M + 1)) := by
    simp only [δ]; field_simp; ring
  rw [e]
  have : (A + B) * M / ((A + B) * M + 1) < 1 := (div_lt_one (by positivity)).2 (lt_add_one _)
  nlinarith

end Uniform

section Comp

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def compKernel (a b : C(X × X, ℂ)) : C(X × X, ℂ) where
  toFun z := ∫ y, a (z.1, y) * b (y, z.2) ∂μ
  continuous_toFun := by
    let _ : UniformSpace X := uniformSpaceOfCompactR1
    exact continuous_integral_mul_of_uniformSpace μ a b

theorem compKernel_apply (a b : C(X × X, ℂ)) (z : X × X) :
    compKernel μ a b z = ∫ y, a (z.1, y) * b (y, z.2) ∂μ := rfl

end Comp

end

end GroundTheory.Automorphic
