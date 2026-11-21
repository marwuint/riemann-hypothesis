import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensVGen

noncomputable section

namespace PI.VolStabW

open MeasureTheory Topology Set Filter

section Cos

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

theorem HasDens.add [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v + φ₂ v) (fun b => g₁ b + g₂ b) := by
  refine ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, fun S hS => ?_⟩
  rw [integral_add h₁.1.integrableOn h₂.1.integrableOn, h₁.2.2 S hS, h₂.2.2 S hS,
    integral_add (h₁.2.1.continuousOn.integrableOn_compact hS)
      (h₂.2.1.continuousOn.integrableOn_compact hS)]

end Cos

end PI.VolStabW
