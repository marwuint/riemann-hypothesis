import Mathlib

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Set Filter Topology Complex MeasureTheory Metric
open scoped Real

namespace LocUnifAnalyticProof

theorem norm_torusMap_sub {D : ℕ} (c : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin D → ℝ)
    (j : Fin D) : ‖torusMap c (fun _ => r) θ j - c j‖ = r := by
  simp [torusMap, abs_of_nonneg hr]

def torusSet {D : ℕ} (c : Fin D → ℂ) (r : ℝ) : Set (Fin D → ℂ) :=
  Set.pi univ fun j => sphere (c j) r

instance {D : ℕ} (c : Fin D → ℂ) (r : ℝ) : CompactSpace (torusSet c r) :=
  isCompact_iff_compactSpace.mp (isCompact_univ_pi fun _ => isCompact_sphere _ _)

end LocUnifAnalyticProof

end GroundTheory.Heights₂.Heights.EffectiveHS
