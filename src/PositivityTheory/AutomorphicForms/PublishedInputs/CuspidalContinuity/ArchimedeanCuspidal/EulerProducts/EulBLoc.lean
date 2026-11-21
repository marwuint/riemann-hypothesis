import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel NNReal

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace Ad3.GP

section Real

theorem val_measurableEmbedding_eulB : MeasurableEmbedding (Units.val : ℝˣ → ℝ) := by
  refine ⟨fun _ _ h => Units.ext h, comap_measurable _, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  have : Units.val '' (Units.val ⁻¹' B : Set ℝˣ) = B ∩ {0}ᶜ := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, by simp⟩
    · rintro ⟨hx, hx0⟩
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [this]
  exact hB.inter (measurableSet_singleton _).compl

theorem map_val_mulR_eulB : Measure.map (Units.val : ℝˣ → ℝ) mulR =
    volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹ := by
  have h := val_measurableEmbedding_eulB.map_comap (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹)
  have hr : Set.range (Units.val : ℝˣ → ℝ) = {0}ᶜ := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      simp
    · intro hx
      exact ⟨Units.mk0 x hx, rfl⟩
  have hac : (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹) ≪ volume :=
    withDensity_absolutelyContinuous _ _
  have h0 : (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹) {0} = 0 := hac (by simp)
  have : (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹).restrict ({0}ᶜ : Set ℝ) =
      volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹ :=
    Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]
      simpa using h0)
  rw [hr, this] at h
  exact h

instance sigmaFinite_mulR_eulB : SigmaFinite mulR := by
  refine SigmaFinite.of_map _ val_measurableEmbedding_eulB.measurable.aemeasurable ?_
  rw [map_val_mulR_eulB]
  exact SigmaFinite.withDensity_ofReal _

end Real

end Ad3.GP
