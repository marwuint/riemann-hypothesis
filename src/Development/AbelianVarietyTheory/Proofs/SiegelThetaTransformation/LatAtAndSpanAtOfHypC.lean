import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanInst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GamAtOfLawsCore
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeightModuleIsLatticeOfShortSeriesSpan

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps GlobalTheory

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.RunLat

theorem thc_le_shortTh {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) : X.Thc s w ≤ X.shortTh w := by
  intro x hx
  simp only [PJ.Thc, PJ.scaled, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply] at hx
  obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hz)

theorem spanAt_of_shortG {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) (β : ℝ) (h : WeightAlgebra.ShortG X w (X.Thc s w) β) : PullbackSections.SpanAt X w := by

  obtain ⟨Sh, hSh, hspan, -⟩ := h
  show Submodule.span _ _ = ⊤
  rw [eq_top_iff, ← hspan]
  exact Submodule.span_mono fun x hx => thc_le_shortTh X s w (hSh hx)

end GlobalTheory.RunLat
