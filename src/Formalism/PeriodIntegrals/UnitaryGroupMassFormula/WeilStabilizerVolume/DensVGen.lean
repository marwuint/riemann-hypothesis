import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.FibFour

noncomputable section

namespace PI.VolStabW

open MeasureTheory Topology Set Filter
open scoped Pointwise

section Dens

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

def HasDens (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (φ : V → ℝ) (g : X → ℝ) :
    Prop :=
  Integrable φ μ ∧ Continuous g ∧ ∀ S : Set X, IsCompact S →
    ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν

theorem HasDens.sub [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v - φ₂ v) (fun b => g₁ b - g₂ b) := by
  refine ⟨h₁.1.sub h₂.1, h₁.2.1.sub h₂.2.1, fun S hS => ?_⟩
  rw [integral_sub h₁.1.integrableOn h₂.1.integrableOn, h₁.2.2 S hS, h₂.2.2 S hS,
    integral_sub (h₁.2.1.continuousOn.integrableOn_compact hS)
      (h₂.2.1.continuousOn.integrableOn_compact hS)]

theorem HasDens.const_mul (c : ℝ) {φ : V → ℝ} {g : X → ℝ} (h : HasDens μ f ι ν φ g) :
    HasDens μ f ι ν (fun v => c * φ v) (fun b => c * g b) := by
  refine ⟨h.1.const_mul c, continuous_const.mul h.2.1, fun S hS => ?_⟩
  rw [integral_const_mul, integral_const_mul, h.2.2 S hS]

theorem nonneg_of_setIntegral [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] (D : X → ℝ) (hD : Continuous D)
    (h0 : ∀ S, IsCompact S → 0 ≤ ∫ b in S, D b ∂ν) (b0 : X) : 0 ≤ D b0 := by
  by_contra hneg
  rw [not_le] at hneg
  have hev : ∀ᶠ b in 𝓝 b0, D b < D b0 / 2 :=
    hD.continuousAt.eventually (gt_mem_nhds (by linarith))
  obtain ⟨S, hSn, hSsub, hSc⟩ := local_compact_nhds hev
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  have hlt : ν S ≠ ⊤ := hSc.measure_lt_top.ne
  have hpos' : 0 < ν.real S := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (ν.measure_pos_of_mem_nhds hSn).ne' hlt
  have hge := setIntegral_ge_of_const_le_real (c := -(D b0 / 2)) (f := fun b => -D b) hSm hlt
    (fun b hb => by
      have : D b < D b0 / 2 := hSsub hb
      linarith)
    (hD.neg.continuousOn.integrableOn_compact hSc)
  rw [integral_neg] at hge
  have := h0 S hSc
  nlinarith

theorem HasDens.le [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
    {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) (hle : ∀ v, φ₁ v ≤ φ₂ v) (b : X) :
    g₁ b ≤ g₂ b := by
  have h := h₂.sub h₁
  have := nonneg_of_setIntegral (ν := ν) _ h.2.1 (fun S hS => by
    rw [← h.2.2 S hS]
    exact integral_nonneg fun v => sub_nonneg.2 (hle v)) b
  linarith

end Dens

end PI.VolStabW
