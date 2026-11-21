import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.RankOneEisenstein.GodementEis
import GroundTheory.GlobalFields.TateThesis.TateMain
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatUniformSummableMajorant

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.EisRk1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRk1Theta

variable {K : Type*} [Field K] [NumberField K]

theorem continuous_setIntegral_of_continuous_uncurry {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (ν : Measure Y)
    [IsFiniteMeasureOnCompacts ν] {E : Set Y} (hE : IsCompact (closure E)) (hν : ν E < ⊤)
    {f : X → Y → ℂ} (hf : Continuous (Function.uncurry f)) :
    Continuous fun x ↦ ∫ u in E, f x u ∂ν := by
  have hint : ∀ x, IntegrableOn (f x) E ν := fun x ↦ by
    have hc : Continuous (f x) := hf.comp (Continuous.prodMk_right x)
    exact (hc.continuousOn.integrableOn_compact hE).mono_set subset_closure
  refine continuous_iff_continuousAt.2 fun q ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  set m := ν.real E with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hδ : 0 < ε / (2 * (m + 1)) := by positivity
  obtain ⟨v, hv, hvu⟩ := hE.mem_uniformity_of_prod (f := f) (s := Set.univ) (q := q)
    hf.continuousOn (Set.mem_univ q) (Metric.dist_mem_uniformity hδ)
  rw [nhdsWithin_univ] at hv
  filter_upwards [hv] with p hp
  rw [dist_eq_norm, ← integral_sub (hint p) (hint q)]
  have hb : ‖∫ u in E, (f p u - f q u) ∂ν‖ ≤ ε / (2 * (m + 1)) * m := by
    refine norm_setIntegral_le_of_norm_le_const hν fun u hu ↦ ?_
    have := hvu p hp u (subset_closure hu)
    rw [Set.mem_setOf_eq, dist_eq_norm] at this
    exact this.le
  refine hb.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.CompanionTheory.EisRk1Theta
