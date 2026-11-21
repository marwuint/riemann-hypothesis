import Formalism.LocalToGlobal.InertKernelTheory.DefsRep
import Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.IteratedFDerivConstSmul

noncomputable section

namespace Formalism.L2.KerInert.Rep

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
open Formalism.MainNotions.FormalGroupSystem (Sys)

theorem isComb_smul (D : D7) (T : Tor D) (e : FamE D) {N N' p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    {F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]} (h : IsComb D T e lam L L' F) {c : ℂ_[p]}
    (hc : ‖c‖ ≤ 1) : IsComb D T e lam L L' (c • F) := by
  obtain ⟨m, r, t, L₁, L₁', hr, ht, hL, rfl⟩ := h
  refine ⟨m, fun k => c * r k, t, L₁, L₁', fun k => ?_, ht, hL, ?_⟩
  · have := hr k
    simp only [IsIntP] at this ⊢
    rw [norm_mul]
    exact mul_le_one₀ hc (norm_nonneg _) this
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, mul_assoc]

theorem isComb_scalar (D : D7) (T : Tor D) (e : FamE D) {N N' p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (G : VC D N N' → ℂ) (h : IsComb D T e lam L L' (pSer D lam G)) {s : ℂ} (hs : s ∈ Qbar) (k : ℤ)
    (hk : ‖(p : ℂ_[p]) ^ k * lamC lam s‖ ≤ 1) :
    IsComb D T e lam L L' (((p : ℂ_[p]) ^ k) • pSer D lam (fun z => s * G z)) := by
  have e1 : ((p : ℂ_[p]) ^ k) • pSer D lam (fun z => s * G z) = ((p : ℂ_[p]) ^ k * lamC lam s) • pSer D lam G := by
    rw [Formalism.L2.PairingIndexBounds.PowerSeriesNecessity.pSer_const_mul D lam hs, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
    rfl
  rw [e1]
  exact isComb_smul D T e lam h hk

end Formalism.L2.KerInert.Rep
