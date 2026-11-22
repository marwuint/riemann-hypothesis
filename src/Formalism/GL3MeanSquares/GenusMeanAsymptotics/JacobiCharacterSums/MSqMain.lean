import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqJac
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqPairs
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqDiagA
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqDiagB
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqCount
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqOrth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqPage
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistB
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistC
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqMainA
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqMainB
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem cN_nonneg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ cN x n := by
  unfold cN
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity))

theorem cN_primePow (x : ℝ) (n : ℕ) (h : cN x n ≠ 0) : IsPrimePow n := by
  unfold cN at h
  exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (left_ne_zero_of_mul h)

theorem RR_nonneg (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (m₀ N : ℕ) : 0 ≤ RR c m₀ N :=
  Finset.sum_nonneg fun n _ => hc n

theorem abs_sum_jacobi_le (PP : Finset ℕ) (s : ℕ) :
    |∑ q ∈ PP, (jacobiSym (q : ℤ) s : ℝ)| ≤ (PP.card : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ q ∈ PP, |(jacobiSym (q : ℤ) s : ℝ)| ≤ 1 := by
    intro q _
    rcases jacobiSym.trichotomy (q : ℤ) s with h | h | h <;> simp [h]
  simpa using Finset.sum_le_sum this

theorem abs_pair_sum_eq (PP : Finset ℕ) (m₀ a₀ n n' : ℕ) (h8 : 8 ∣ m₀) (ha : a₀.Coprime m₀) (hn : 0 < n)
    (hn' : 0 < n') (hPP : ∀ q ∈ PP, q.Prime ∧ q % m₀ = a₀ % m₀ ∧ n * n' < q) :
    |∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| =
      |∑ q ∈ PP, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ)| := by
  obtain ⟨σ, hσ, h⟩ := jacobi_class m₀ a₀ (n * n') h8 ha (Nat.mul_pos hn hn')
  have h1 : ∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ) =
      (σ : ℝ) * ∑ q ∈ PP, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨hp, hm, hlt⟩ := hPP q hq
    have := h q hp hm hlt
    rw [← jacobiSym.mul_left, ← Int.cast_mul, ← this]
    push_cast
    rfl
  rw [h1, abs_mul]
  rcases hσ with h | h <;> simp [h]

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
