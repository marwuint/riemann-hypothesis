import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TauPlBijective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralSubst
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPowDivFactorialLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeOfLiesOver
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Classical
namespace GlobalTheory.CompareInert

section Rings

open Formalism.MainNotions.GL3Theta

variable {l : ℕ} [Fact l.Prime]

theorem mem_Wp_of_kur {x : ℂ_[l]} (hx : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l) (h1 : ‖x‖ ≤ 1) : x ∈ Wp l := by
  have hp : l.Prime := Fact.out
  have hB := ((Formalism.L2.Th1.D.kurIntegers l).1 x).2 ⟨hx, h1⟩
  have hS : Formalism.L2.Th1.D.muPrime l = {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} := by
    ext ζ
    simp only [Formalism.L2.Th1.D.muPrime, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn), h⟩
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp hn), h⟩
  unfold Formalism.L2.Th1.D.ringB Formalism.L2.Th1.D.ringA at hB
  rw [hS] at hB
  exact hB

theorem Wp_subset_Kur {x : ℂ_[l]} (hx : x ∈ Wp l) : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
  refine closure_mono (s := ((Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} : Subring ℂ_[l]) : Set ℂ_[l])) ?_ hx
  intro y hy
  have hle : Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} ≤
      (Subfield.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1}).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro ζ ⟨n, h0, hn, h⟩
    exact Subfield.subset_closure ⟨n, h0, (Nat.Prime.coprime_iff_not_dvd Fact.out).mp (Nat.coprime_comm.mp hn), h⟩
  exact hle hy

theorem exists_pow_norm_le {K : Type*} [NormedField K] {a : K} (ha : ‖a‖ < 1) (x : K) : ∃ k : ℕ, ‖a ^ k * x‖ ≤ 1 := by
  by_cases hr : x = 0
  · exact ⟨0, by simp [hr]⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 hr)) ha
  refine ⟨k, ?_⟩
  rw [norm_mul, norm_pow]
  have h0 : 0 < ‖x‖ := norm_pos_iff.2 hr
  calc ‖a‖ ^ k * ‖x‖ ≤ ‖x‖⁻¹ * ‖x‖ := by gcongr
    _ = 1 := inv_mul_cancel₀ h0.ne'

theorem norm_l_lt : ‖(l : ℂ_[l])‖ < 1 := by
  have h : ‖(l : ℂ_[l])‖ = ‖(l : ℚ_[l])‖ := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l]
    exact norm_algebraMap' ℂ_[l] _
  rw [h]
  exact Padic.norm_p_lt_one

end Rings

end GlobalTheory.CompareInert
