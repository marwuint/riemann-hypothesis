import Formalism.LocalToGlobal.InertKernelTheory.ScalG
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.SameChart

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.ScalM

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F

section lamC

variable {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p])

theorem qbar_zpow_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (n : ℤ) : s ^ n ∈ TaylorLogMetric.Qbar := by
  cases n with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hs k
  | negSucc k =>
    rw [zpow_negSucc]
    exact inv_mem (pow_mem hs _)

theorem lamC_of_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) : TaylorLogMetric.lamC lam s = lam ⟨s, hs⟩ := by
  unfold TaylorLogMetric.lamC
  rw [dif_pos hs]

theorem lamC_mul_mem {s t : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (ht : t ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (s * t) = TaylorLogMetric.lamC lam s * TaylorLogMetric.lamC lam t := by
  rw [lamC_of_mem lam (TaylorLogMetric.Qbar.mul_mem hs ht), lamC_of_mem lam hs, lamC_of_mem lam ht, ← map_mul]
  rfl

theorem lamC_inv_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) : TaylorLogMetric.lamC lam s⁻¹ = (TaylorLogMetric.lamC lam s)⁻¹ := by
  rw [lamC_of_mem lam (TaylorLogMetric.Qbar.inv_mem hs), lamC_of_mem lam hs, ← map_inv₀]
  rfl

theorem lamC_zpow_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (n : ℤ) : TaylorLogMetric.lamC lam (s ^ n) = (TaylorLogMetric.lamC lam s) ^ n := by
  rw [lamC_of_mem lam (qbar_zpow_mem hs n), lamC_of_mem lam hs, ← map_zpow₀]
  rfl

end lamC

end Formalism.L2.KerInert.ScalM

namespace Formalism.L2.KerInert.ScalM

end Formalism.L2.KerInert.ScalM
