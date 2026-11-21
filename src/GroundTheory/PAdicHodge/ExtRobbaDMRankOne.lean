import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaFrob
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Polynomial Laurent Filter Topology

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem convergesAt_of_forall_weight_le {x : Γ} {ρ σ Y : ℝ} (hσ0 : 0 < σ) (hσρ : σ < ρ)
    (h : ∀ n : ℕ, ‖T.coeff x n‖ * ρ ^ n ≤ Y) : ConvergesAt (T.zcoeff x) σ := by
  have hρ0 : 0 < ρ := hσ0.trans hσρ
  have hY : 0 ≤ Y := (mul_nonneg (norm_nonneg _) (pow_pos hρ0 0).le).trans (h 0)
  have hsr0 : 0 ≤ σ / ρ := by positivity
  have hsr1 : σ / ρ < 1 := by rwa [div_lt_one hρ0]
  refine convergesAt_of_eventually hσ0 (T.zcoeff_neg_exists x) fun ε hε => ?_
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (Y + 1) by positivity) hsr1
  refine ⟨K, fun n hn => ?_⟩
  lift n to ℕ using (by omega)
  rw [zcoeff_natCast, zpow_natCast]
  have hn' : K ≤ n := by exact_mod_cast hn
  calc ‖T.coeff x n‖ * σ ^ n = (‖T.coeff x n‖ * ρ ^ n) * (σ / ρ) ^ n := by
        rw [div_pow]; field_simp
    _ ≤ Y * (σ / ρ) ^ K :=
        mul_le_mul (h n) (pow_le_pow_of_le_one hsr0 hsr1.le hn') (by positivity) hY
    _ ≤ (Y + 1) * (ε / (Y + 1)) := mul_le_mul (by linarith) hK.le (by positivity) (by linarith)
    _ = ε := by field_simp

namespace TeichFrob

end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem exists_eq_π_pow_mul {x : Γ} (hx : x ≠ 0) :
    ∃ (m : ℕ) (x' : Γ), x = T.π ^ m * x' ∧ T.red x' ≠ 0 ∧
      T.zcoeff x' = fun j => T.zcoeff x (j + m) := by
  classical
  have hex : ∃ n, T.coeff x n ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hx (T.eq_of_coeff_eq (funext fun n => by rw [h n, coeff_zero_elem]))
  set m := Nat.find hex
  have hlt : ∀ i < m, T.coeff x i = 0 := fun i hi => not_not.1 (Nat.find_min hex hi)
  have hps : T.partialSum x m = 0 := by
    simp only [partialSum, finSum]
    exact Finset.sum_eq_zero fun i hi => by rw [hlt i (Finset.mem_range.1 hi), map_zero, mul_zero]
  have heq : x = T.π ^ m * T.tail^[m] x := by
    have := T.sub_partialSum x m; rwa [hps, sub_zero] at this
  refine ⟨m, T.tail^[m] x, heq, Nat.find_spec hex, ?_⟩
  funext j
  conv_rhs => rw [heq]
  exact (T.zcoeff_π_pow_mul m _ j).symm

namespace TeichFrob

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
