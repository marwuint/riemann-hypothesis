import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistOfCuspParams
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesRationalityAndCoefficientBound

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.PlaceRead.SeriesAtState

theorem low_of_tiedC {D : D7} {Fr : TwFrameC D} (h : TwistFrameLowIndexCompatibility D Fr (lowAll D)) (i) (P : PlE D.host)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') : ℕ) :
      𝓞 D.host.E) ∈ P.asIdeal) : P ∈ D.ntw.S0 i := by
  have hp := P.isPrime
  have mem : ∀ p ∈ lowAll D, ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → P ∈ D.ntw.S0 i := fun p a b => by
    rw [← Finset.mem_coe, h.ringSpec_excludedPlaces_eq i]
    exact Or.inr (h.concreteTwistFrame_extraExcluded_over_smallPrimes i p a b)
  have key : ∀ m : ℕ, m ≠ 0 → ((m : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    intro m
    induction m using Nat.recOnMul with
    | zero => exact fun h0 => absurd rfl h0
    | one => exact fun _ h1 => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h1)) hp.ne_top
    | prime p pp => exact fun _ h1 => ⟨p, pp, dvd_rfl, h1⟩
    | mul a b iha ihb =>
      intro h0 h1
      rw [Nat.cast_mul] at h1
      rcases hp.mem_or_mem h1 with h1 | h1
      · obtain ⟨p, p1, p2, p3⟩ := iha (left_ne_zero_of_mul h0) h1
        exact ⟨p, p1, p2.mul_right _, p3⟩
      · obtain ⟨p, p1, p2, p3⟩ := ihb (right_ne_zero_of_mul h0) h1
        exact ⟨p, p1, p2.mul_left _, p3⟩
  simp only [Nat.cast_mul] at hP
  rcases hp.mem_or_mem hP with hP | hP
  · rcases hp.mem_or_mem hP with hP | hP
    · rcases hp.mem_or_mem hP with hP | hP
      · obtain ⟨p, p1, p2, p3⟩ := key _ D.host.QS_pos.ne' hP
        refine mem p (Finset.mem_union_left _ ?_) p3
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_))
        exact Nat.mem_primeFactors.2 ⟨p1, (D.host.dvd_natAbs_discr_iff p1).2 (p2.trans D.host.QS_dvd_condN),
          Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)⟩
      · refine mem _ (Finset.mem_union_left _ ?_) hP
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_))
        exact Nat.mem_primeFactors.2 ⟨D.host.hyp.1, GlobalTheory.TwInputs.JoinModel.q_dvd_discr D,
          Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)⟩
    · have hN : Ideal.absNorm D.host.ccK ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
      obtain ⟨p, p1, p2, p3⟩ := key _ hN hP
      refine mem p (Finset.mem_union_left _ ?_) p3
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨p1, p2, hN⟩)))
  · rcases hp.mem_or_mem hP with hP | hP
    · rcases hp.mem_or_mem hP with hP | hP
      · rcases hp.mem_or_mem hP with hP | hP
        · exact mem _ (by simp [lowAll]) hP
        · exact mem _ (by simp [lowAll]) hP
      · exact mem _ (by simp [lowAll]) hP
    · exact mem _ (by simp [lowAll]) hP

end GlobalTheory.PlaceRead.SeriesAtState
