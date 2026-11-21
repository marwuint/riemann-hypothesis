import Formalism.LocalRingCardinality.DataMink
import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial

namespace Formalism.BasicNotions

open Formalism.HermitianLatticeCounting.S6 (minkowskiM minkowskiExp)

theorem minkM_pos (n : ℕ) : 0 < minkM n :=
  Finset.prod_pos fun _ hp => pow_pos (Finset.mem_filter.1 hp).2.pos _

theorem minkM_dvd_factorial (n : ℕ) : minkM n ∣ (2 * n).factorial := Formalism.HermitianLatticeCounting.P.minkowski_number_dvd_factorial n

theorem log_minkM_le_two (n : ℕ) : Real.log (minkM n : ℝ) ≤ 2 * n * Real.log (2 * n) := by
  have h1 : minkM n ≤ (2 * n) ^ (2 * n) :=
    (Nat.le_of_dvd (Nat.factorial_pos _) (minkM_dvd_factorial n)).trans (Nat.factorial_le_pow _)
  have h2 : (minkM n : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ (2 * n) := by exact_mod_cast h1
  have h3 : (0 : ℝ) < minkM n := by exact_mod_cast minkM_pos n
  have h4 := Real.log_le_log h3 h2
  rw [Real.log_pow] at h4
  push_cast at h4
  exact h4

theorem Ranks.two_le_fN (R : Ranks) : 2 ≤ R.f * R.N R.m := by
  have hf : 2 ≤ R.f := by
    have h1 := R.two_le_m
    have h2 := R.m_le_f
    unfold Ranks.f Ranks.n; omega
  have hN : 1 ≤ R.N R.m := by
    have h1 := R.k_ge
    have h2 : R.k ≤ R.N R.m := Nat.le_add_right _ _
    omega
  calc 2 = 2 * 1 := rfl
    _ ≤ R.f * R.N R.m := Nat.mul_le_mul hf hN

theorem DGamMink.mem {D : D7} (h : DGamMink D) (hD : DGamDef D) (u : D.what₂.Word) :
    (D.mem u).C.DGam = minkM (2 * D.R.f * D.R.N D.R.m) := by
  rw [← hD.one u D.u₀ D.what₂.mu0, hD.one D.u₀ D.u₀ D.what₂.mu0]; exact h

theorem DGamMink.chTw {D : D7} (h : DGamMink D) (hD : DGamDef D) (u : D.what₂.Word) (μ : D.what₂.Tup) :
    (D.chTw u μ).DGam = minkM (2 * D.R.f * D.R.N D.R.m) :=
  (hD.one D.u₀ u μ).trans h

end Formalism.BasicNotions
