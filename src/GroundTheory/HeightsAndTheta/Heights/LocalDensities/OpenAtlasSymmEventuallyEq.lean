import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff

def openAtlas {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω) :
    FinHolAtlas D Ω where
  n := 1
  chart _ := Ω.openPartialHomeomorphSubtypeCoe hΩ
  cover _ := ⟨0, by simp⟩
  holo _ _ := by
    intro y hy
    have hy' : y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target := hy.1
    have hev : (Ω.openPartialHomeomorphSubtypeCoe hΩ ∘ (Ω.openPartialHomeomorphSubtypeCoe hΩ).symm)
        =ᶠ[𝓝 y] id := by
      filter_upwards [(Ω.openPartialHomeomorphSubtypeCoe hΩ).open_target.mem_nhds hy'] with z hz
      exact (Ω.openPartialHomeomorphSubtypeCoe hΩ).right_inv hz
    exact analyticAt_id.congr hev.symm

instance {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω) :
    Subsingleton (Fin (openAtlas Ω hΩ).n) :=
  (inferInstance : Subsingleton (Fin 1))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
