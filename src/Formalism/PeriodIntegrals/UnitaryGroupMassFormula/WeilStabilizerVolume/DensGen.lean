import Mathlib
import Formalism.PeriodIntegrals.VolFromSW

noncomputable section

namespace PI.VolStabW.DensGen

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}

theorem eq_zero_of_setIntegral [LocallyCompactSpace X] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] (D : X → ℝ) (W : Set X) (b0 : X) (hW : W ∈ 𝓝 b0)
    (hD : ContinuousOn D W) (h0 : ∀ S, IsCompact S → S ⊆ W → ∫ b in S, D b ∂ν = 0) :
    D b0 = 0 := by
  have key : ∀ D : X → ℝ, ContinuousOn D W →
      (∀ S, IsCompact S → S ⊆ W → ∫ b in S, D b ∂ν = 0) → ¬ 0 < D b0 := by
    intro D hD h0 hpos
    have hev : ∀ᶠ b in 𝓝 b0, D b0 / 2 < D b :=
      (hD.continuousAt hW).eventually (lt_mem_nhds (by linarith))
    obtain ⟨S, hSn, hSsub, hSc⟩ := local_compact_nhds (inter_mem hW hev)
    have hSm : MeasurableSet S := hSc.isClosed.measurableSet
    have hlt : ν S ≠ ⊤ := hSc.measure_lt_top.ne
    have hpos' : 0 < ν.real S := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (ν.measure_pos_of_mem_nhds hSn).ne' hlt
    have hge := setIntegral_ge_of_const_le_real (c := D b0 / 2) hSm hlt
      (fun b hb => (hSsub hb).2.le)
      ((hD.mono fun b hb => (hSsub hb).1).integrableOn_compact hSc)
    rw [h0 S hSc fun b hb => (hSsub hb).1] at hge
    nlinarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · refine key (fun b => -D b) hD.neg (fun S hS hSW => ?_) (by linarith)
    rw [integral_neg, h0 S hS hSW, neg_zero]
  · exact key D hD h0 h

end PI.VolStabW.DensGen
