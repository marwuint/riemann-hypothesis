import Mathlib

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Set Filter Topology Complex MeasureTheory Metric
open scoped Real

namespace LocUnifAnalyticProof

theorem norm_torusMap_sub {D : ℕ} (c : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin D → ℝ)
    (j : Fin D) : ‖torusMap c (fun _ => r) θ j - c j‖ = r := by
  simp [torusMap, abs_of_nonneg hr]

theorem continuous_torusMap' {D : ℕ} (c : Fin D → ℂ) (R : Fin D → ℝ) :
    Continuous (torusMap c R) := by
  unfold torusMap; fun_prop

def torusSet {D : ℕ} (c : Fin D → ℂ) (r : ℝ) : Set (Fin D → ℂ) :=
  Set.pi univ fun j => sphere (c j) r

instance {D : ℕ} (c : Fin D → ℂ) (r : ℝ) : CompactSpace (torusSet c r) :=
  isCompact_iff_compactSpace.mp (isCompact_univ_pi fun _ => isCompact_sphere _ _)

theorem torusMap_mem {D : ℕ} (c : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin D → ℝ) :
    torusMap c (fun _ => r) θ ∈ torusSet c r := fun j _ => by
  rw [mem_sphere, dist_eq_norm]; exact norm_torusMap_sub c hr θ j

theorem continuous_torusMap_comp {D : ℕ} (c : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (κ : C(torusSet c r, ℂ)) :
    Continuous fun θ : Fin D → ℝ => κ ⟨torusMap c (fun _ => r) θ, torusMap_mem c hr θ⟩ :=
  κ.continuous.comp ((continuous_torusMap' c _).subtype_mk _)

noncomputable def boxIntegral {D : ℕ} (c : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    C(torusSet c r, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun κ => ∫ θ in Icc (0 : Fin D → ℝ) (fun _ => 2 * π),
        κ ⟨torusMap c (fun _ => r) θ, torusMap_mem c hr θ⟩
      map_add' := fun κ μ => by
        simp only [ContinuousMap.add_apply]
        exact integral_add
          ((continuous_torusMap_comp c hr κ).continuousOn.integrableOn_compact isCompact_Icc)
          ((continuous_torusMap_comp c hr μ).continuousOn.integrableOn_compact isCompact_Icc)
      map_smul' := fun a κ => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul a _ }
    (volume.real (Icc (0 : Fin D → ℝ) fun _ => 2 * π))
    (fun κ => (norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (Fin D → ℝ)))
        measure_Icc_lt_top fun θ _ => κ.norm_coe_le_norm _).trans_eq (mul_comm _ _))

theorem boxIntegral_apply {D : ℕ} (c : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r) (κ : C(torusSet c r, ℂ)) :
    boxIntegral c hr κ = ∫ θ in Icc (0 : Fin D → ℝ) (fun _ => 2 * π),
        κ ⟨torusMap c (fun _ => r) θ, torusMap_mem c hr θ⟩ := rfl

end LocUnifAnalyticProof

end GroundTheory.Heights₂.Heights.EffectiveHS
