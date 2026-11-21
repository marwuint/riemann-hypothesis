import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientModelTopClassesMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianGrowthConjTorsionTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstJetOperatorNormCauchyBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyParameterSizesTestChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

noncomputable section

namespace GlobalTheory.KerConjMean

theorem pow_le_exp_posLog (x : ℝ) (g : ℕ) : x ^ g ≤ Real.exp (g * Real.posLog x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases g with _ | g
    · simp
    · rw [zero_pow (Nat.succ_ne_zero g)]; exact (Real.exp_pos _).le
  · calc x ^ g ≤ |x ^ g| := le_abs_self _
      _ = |x| ^ g := abs_pow x g
      _ = Real.exp (g * Real.log |x|) := by
          rw [← Real.log_pow, Real.exp_log (pow_pos (abs_pos.2 hx) g)]
      _ ≤ Real.exp (g * Real.posLog x) := by
          gcongr
          rw [Real.log_abs]; unfold Real.posLog; exact le_max_right _ _

theorem max_pow_le_exp_posLog (A : ℝ) (hA : 0 < A) (d : ℕ) :
    max 1 A⁻¹ ^ d ≤ Real.exp (d * Real.posLog A⁻¹) := by
  have h1 : max 1 A⁻¹ ≤ Real.exp (Real.posLog A⁻¹) := by
    refine max_le ?_ ?_
    · exact Real.one_le_exp (by unfold Real.posLog; exact le_max_left _ _)
    · calc A⁻¹ = Real.exp (Real.log A⁻¹) := (Real.exp_log (inv_pos.2 hA)).symm
        _ ≤ Real.exp (Real.posLog A⁻¹) := by gcongr; unfold Real.posLog; exact le_max_right _ _
  calc max 1 A⁻¹ ^ d ≤ Real.exp (Real.posLog A⁻¹) ^ d := pow_le_pow_left₀ (by positivity) h1 d
    _ = Real.exp (d * Real.posLog A⁻¹) := (Real.exp_nat_mul _ d).symm

theorem size_bound (K f N b rd Kx W1 W2 a bb c : ℝ) (g : ℕ) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hcf : c ≤ f) (hb3 : 3 ≤ b) (hN1 : 1 ≤ N) (hNb : N ≤ b)
    (hf1 : 1 ≤ f) (hfb : f ≤ b) (hrd0 : 0 ≤ rd) (hrd : rd ≤ b) (ha0 : 0 ≤ a) (haN : a ≤ N) (hbb0 : 0 ≤ bb)
    (hbN : bb ≤ N) (hW1 : W1 ≤ f * N * (8 * b)) (hW2 : W2 ≤ f * N * (8 * b)) (hW10 : 0 ≤ W1) (hW20 : 0 ≤ W2)
    (hg : (g : ℝ) = f * a * bb) (hKx : 0 < Kx)
    (hlogKx : Real.log Kx ≤ K * (W1 + W2 + c * (a + bb) ^ 2 + 1) * Real.log (2 + W1 + W2 + a + bb + c)) :
    Real.log (3 * (2 * (g : ℝ) * rd + 1) ^ g * Kx) ≤ (6 + 126 * K) * f * N * b * Real.log b ∧
      (g : ℝ) ≤ f * N * b := by
  have hb0 : 0 < b := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hlogb : 1 ≤ Real.log b := by
    have : Real.exp 1 ≤ b := by linarith [Real.exp_one_lt_d9]
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hfN1 : 1 ≤ f * N := one_le_mul_of_one_le_of_one_le hf1 hN1
  have hfNb : 1 ≤ f * N * b := by nlinarith
  have hab : a * bb ≤ N * N := mul_le_mul haN hbN hbb0 hN0
  have hfNN : f * a * bb ≤ f * N * N := by
    have := mul_le_mul_of_nonneg_left hab hf0
    linarith
  have hNN : f * N * N ≤ f * N * b := mul_le_mul_of_nonneg_left hNb (by positivity)
  have hgG : (g : ℝ) ≤ f * N * b := by rw [hg]; linarith
  have hfNb3 : f * N * b ≤ b ^ 3 := by
    have h1 := mul_le_mul hfb hNb hN0 hb0.le
    have h2 := mul_le_mul_of_nonneg_right h1 hb0.le
    calc f * N * b ≤ b * b * b := h2
      _ = _ := by ring
  have hg3 : (g : ℝ) ≤ b ^ 3 := hgG.trans hfNb3
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hrdpos : 0 < 2 * (g : ℝ) * rd + 1 := by have := mul_nonneg (mul_nonneg zero_le_two hg0) hrd0; linarith
  have hq : 2 * (g : ℝ) * rd + 1 ≤ 3 * b ^ 4 := by
    have h1 := mul_le_mul hg3 hrd hrd0 (by positivity)
    have h2 : (1 : ℝ) ≤ b ^ 4 := one_le_pow₀ (by linarith)
    have h3 : b ^ 3 * b = b ^ 4 := by ring
    linarith
  have hl3 : Real.log 3 ≤ Real.log b := Real.log_le_log (by norm_num) hb3
  have hlq : Real.log (2 * (g : ℝ) * rd + 1) ≤ 5 * Real.log b := by
    calc _ ≤ Real.log (3 * b ^ 4) := Real.log_le_log hrdpos hq
      _ = Real.log 3 + 4 * Real.log b := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ _ := by linarith
  have hlq0 : 0 ≤ Real.log (2 * (g : ℝ) * rd + 1) := Real.log_nonneg (by
    have := mul_nonneg (mul_nonneg zero_le_two hg0) hrd0; linarith)
  have hY0 : 0 ≤ f * N * b * Real.log b := by positivity
  have hgl : (g : ℝ) * Real.log (2 * (g : ℝ) * rd + 1) ≤ 5 * (f * N * b * Real.log b) := by
    have := mul_le_mul hgG hlq hlq0 (by positivity); linarith
  have hKb : Real.log Kx ≤ 126 * K * (f * N * b * Real.log b) := by
    have hsq : (a + bb) ^ 2 ≤ (2 * N) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hab2 : c * (a + bb) ^ 2 ≤ 4 * (f * N * b) := by
      have := mul_le_mul hcf hsq (by positivity) hf0
      have e : f * (2 * N) ^ 2 = 4 * (f * N * N) := by ring
      linarith
    have hQ1 : W1 + W2 + c * (a + bb) ^ 2 + 1 ≤ 21 * (f * N * b) := by linarith
    have hQ1' : 0 ≤ W1 + W2 + c * (a + bb) ^ 2 + 1 := by positivity
    have hArg0 : 0 < 2 + W1 + W2 + a + bb + c := by linarith
    have hb27 : (27 : ℝ) ≤ b ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hb3 3; norm_num at this; linarith
    have hbb3 : b ≤ b ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have hArg : 2 + W1 + W2 + a + bb + c ≤ 27 * b ^ 3 := by linarith
    have hQ2 : Real.log (2 + W1 + W2 + a + bb + c) ≤ 6 * Real.log b := by
      calc _ ≤ Real.log (27 * b ^ 3) := Real.log_le_log hArg0 hArg
        _ = 3 * Real.log 3 + 3 * Real.log b := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
              show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
        _ ≤ _ := by linarith
    have hQ20 : 0 ≤ Real.log (2 + W1 + W2 + a + bb + c) := Real.log_nonneg (by linarith)
    have := mul_le_mul (mul_le_mul_of_nonneg_left hQ1 hK0) hQ2 hQ20 (by positivity)
    refine hlogKx.trans (this.trans (le_of_eq ?_))
    ring
  refine ⟨?_, hgG⟩
  rw [Real.log_mul (by positivity) hKx.ne', Real.log_mul (by norm_num) (pow_pos hrdpos g).ne', Real.log_pow]
  have hlY : Real.log b ≤ f * N * b * Real.log b := le_mul_of_one_le_left (by linarith) hfNb
  have e : (6 + 126 * K) * f * N * b * Real.log b =
      f * N * b * Real.log b + 5 * (f * N * b * Real.log b) + 126 * K * (f * N * b * Real.log b) := by ring
  rw [e]; linarith

end GlobalTheory.KerConjMean

end
