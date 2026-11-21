import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsBaseJointFld
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpreadLamOfLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardDvdCardGL
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHcParamOfCode
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevChOfLevelPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStdLarge
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsFamPOfKits
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MPowFiveMulFMulLLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt

noncomputable section

namespace GlobalTheory.Mem.Top.Inh

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem g_big (eps : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (g : ℕ), s.eps = eps → x0 ≤ s.x →
    RankVal s R → ((R.k : ℝ) * s.b) ^ 8 ≤ g → 2 * R.f * R.k < g - 1 := by
  obtain ⟨x3, hx3⟩ := rank_basic_bounds eps h0 h1
  obtain ⟨x4, hx4⟩ := GlobalTheory.scale_poly_comparison eps 4 1 h0 one_pos
  refine ⟨max x3 (max x4 10), fun s R g he hx hR hg => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨y3, y4, y5⟩ := hx
  obtain ⟨hf, -⟩ := hx3 s R he y3 hR
  obtain ⟨-, -, hb, -⟩ := hx4 s he y4
  have hx0 : 0 < s.x := by linarith
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (by positivity)
  have hk3 := R.m_add_three_le_k
  have pw : ∀ n : ℕ, s.x ^ (n : ℝ) = s.x ^ n := fun n => Real.rpow_natCast _ _
  have hf' : (R.f : ℝ) ≤ s.x ^ 3 := by rw [← pw]; exact_mod_cast hf
  have hb' : s.x ^ 4 ≤ s.b := by
    rw [Real.rpow_one] at hb
    rw [← pw]
    exact le_trans (by exact_mod_cast le_mul_of_one_le_right (by positivity) hX1) hb
  have h3 : 1 ≤ s.x ^ 3 := one_le_pow₀ (by linarith)
  have h4 : 10 * s.x ^ 3 ≤ s.b := by
    calc 10 * s.x ^ 3 ≤ s.x * s.x ^ 3 := mul_le_mul_of_nonneg_right y5 (by positivity)
      _ = s.x ^ 4 := by ring
      _ ≤ s.b := hb'
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 1 ≤ R.k)
  have c1 : (R.k : ℝ) * s.b ≤ g :=
    (le_self_pow₀ (one_le_mul_of_one_le_of_one_le hk1 (by linarith)) (by norm_num)).trans hg
  have c3 : ((2 * R.f * R.k + 1 : ℕ) : ℝ) < g := by
    have d1 := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ R.k by positivity)
    have d2 := mul_le_mul_of_nonneg_left hf' (show (0 : ℝ) ≤ R.k by positivity)
    have d3 := one_le_mul_of_one_le_of_one_le hk1 h3
    push_cast
    nlinarith
  have c4 : 2 * R.f * R.k + 1 < g := by exact_mod_cast c3
  omega

end GlobalTheory.Mem.Top.Inh

end
