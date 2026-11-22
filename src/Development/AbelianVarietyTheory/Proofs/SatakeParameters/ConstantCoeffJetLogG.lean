import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPowDivFactorialLe
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.BeProps

open MvPowerSeries GlobalTheory.ThStr Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ}

theorem norm_eq_one_of_pow {n : ℕ} (hn : 0 < n) {a : ℂ_[l]} (ha : a ^ n = 1) : ‖a‖ = 1 := by
  have h : ‖a‖ ^ n = 1 := by rw [← norm_pow, ha, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) hn.ne').1 h

theorem norm_le_one_of_mem_Wp {w : ℂ_[l]} (hw : w ∈ Wp l) : ‖w‖ ≤ 1 := by
  have hc : IsClosed {x : ℂ_[l] | ‖x‖ ≤ 1} := isClosed_le continuous_norm continuous_const
  refine closure_minimal (t := {x : ℂ_[l] | ‖x‖ ≤ 1}) (fun x hx => ?_) hc hw
  change ‖x‖ ≤ 1
  induction hx using Subring.closure_induction with
  | mem x hx => obtain ⟨n, hn, -, h⟩ := hx; exact (norm_eq_one_of_pow hn h).le
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | neg x _ hx => simpa using hx
  | mul x y _ _ hx hy => rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

variable [NeZero d]

theorem constantCoeff_laS (s : ZMod d) : constantCoeff (laS l d s) = 0 :=
  (GlobalTheory.BiextInhab.laK_idMod2 (K := ℂ_[l]) (d := d) hl.out).1 s

theorem constantCoeff_laAt {κ : Type} [Finite κ] (ι : ZMod d → κ) (s : ZMod d) :
    constantCoeff (laAt (l := l) ι s) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) (constantCoeff_laS s)

theorem coeff_subst_range {K σ : Type*} [CommRing K] {G : MvPowerSeries σ K}
    (hG : MvPowerSeries.constantCoeff G = 0) (f : PowerSeries K) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (f.subst G) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
        PowerSeries.coeff n f * MvPowerSeries.coeff α (G ^ n) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hG),
    finsum_eq_sum_of_support_subset (s := Finset.range ((α.sum fun _ k => k) + 1))]
  · rfl
  · intro k hk
    by_contra h
    apply hk
    have hlt : (α.sum fun _ k => k) < k := by simpa using h
    have h0 : MvPowerSeries.coeff α (G ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hG)
      exact_mod_cast hlt
    simp [h0]

theorem expMv_eq_subst {σ : Type*} {G : MvPowerSeries σ ℂ_[l]} (hG : MvPowerSeries.constantCoeff G = 0) :
    expMv G = (PowerSeries.exp ℂ_[l]).subst G := by
  ext α
  rw [coeff_subst_range hG]
  show expMv G α = _
  rw [expMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [div_eq_inv_mul]

theorem subst_psubst {σ τ : Type} [Finite σ] {b : σ → MvPowerSeries τ ℂ_[l]} (hb : HasSubst b)
    {f : MvPowerSeries σ ℂ_[l]} (hf : constantCoeff f = 0) (g : PowerSeries ℂ_[l]) :
    subst b (PowerSeries.subst f g) = PowerSeries.subst (subst b f) g := by
  have ha : HasSubst (fun _ : Unit => f) := hasSubst_of_constantCoeff_zero fun _ => hf
  unfold PowerSeries.subst
  rw [subst_comp_subst_apply ha hb]

end GlobalTheory.BeProps
