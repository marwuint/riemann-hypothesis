import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts

open Filter Topology

namespace GlobalTheory.PSerLin

theorem map_subst_linear {σ κ R S : Type*} [Finite σ] [Fintype κ] [CommRing R] [CommRing S]
    (h : R →+* S) (c : σ → κ → R) (F : MvPowerSeries σ R) :
    MvPowerSeries.map h (MvPowerSeries.subst
      (fun k => ∑ x, MvPowerSeries.C (c k x) * (MvPowerSeries.X x : MvPowerSeries κ R)) F) =
    MvPowerSeries.subst
      (fun k => ∑ x, MvPowerSeries.C (h (c k x)) * (MvPowerSeries.X x : MvPowerSeries κ S))
      (MvPowerSeries.map h F) := by
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp)]
  simp

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField

open Classical in

theorem taylorDir_linear (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ)
    (c : D.what₂.Tau × Fin N' × Fin N → D.what₂.Tau × Fin N' × Fin N → ℂ)
    (hG : Differentiable ℂ G) :
    taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) (fun z : VC D N N' => G (fun τ i j =>
      ∑ x : D.what₂.Tau × Fin N' × Fin N, c (τ, i, j) x * z x.1 x.2.1 x.2.2)) =
    MvPowerSeries.subst (fun k => ∑ x, MvPowerSeries.C (c k x) *
      (MvPowerSeries.X x : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ))
      (taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) G) := by
  let L : (D.what₂.Tau × Fin N' × Fin N → ℂ) →L[ℂ] VC D N N' :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b =>
      ContinuousLinearMap.proj (τ, a, b)
  have hL : ∀ z τ a b, L z τ a b = z (τ, a, b) := fun _ _ _ _ => rfl
  have hc : Formalism.MainNotions.TaylorLogMetric.coordV D = fun k => L (Pi.single k 1) := by
    funext ⟨k1, k2, k3⟩ τ a b
    simp [hL, Formalism.MainNotions.TaylorLogMetric.coordV, Pi.single_apply]
  have han : AnalyticAt ℂ G 0 :=
    SCV.analyticAt_iff_eventually_differentiableAt.2 (Eventually.of_forall hG)
  have han' : AnalyticAt ℂ (fun z => G (L z)) 0 :=
    han.comp_of_eq (L.analyticAt 0) (map_zero L)
  let ev : (D.what₂.Tau × Fin N' × Fin N) → (VC D N N' →L[ℂ] ℂ) := fun x =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) x.2.2).comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N' => Fin N → ℂ) x.2.1).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : D.what₂.Tau => Fin N' → Fin N → ℂ) x.1))
  let ℓ : (D.what₂.Tau × Fin N' × Fin N) → (VC D N N' →L[ℂ] ℂ) := fun k => ∑ x, c k x • ev x
  have hℓ : ∀ k z, ℓ k z = ∑ x, c k x * z x.1 x.2.1 x.2.2 := fun k z => by
    simp [ℓ, ev]
  have h := taylorDir_comp (Formalism.MainNotions.TaylorLogMetric.coordV D) (φ := fun z k => ℓ k z)
    (analyticAt_pi_iff.2 fun k => (ℓ k).analyticAt 0) (funext fun k => map_zero (ℓ k)) han'
  rw [taylor_comp_clm L han, ← hc] at h
  convert h using 2
  · funext z
    refine congrArg G ?_
    funext τ i j
    exact (hℓ (τ, i, j) z).symm
  · funext k
    rw [show (fun z => ℓ k z) = ⇑(ℓ k) from rfl, taylorDir_clm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPowerSeries.smul_eq_C_mul, hℓ, hc]
    simp [hL, Pi.single_apply]

end GlobalTheory.PSerLin
