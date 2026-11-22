import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CosetExpUnique
import Formalism.LocalRingCardinality.SpanPowerMembership.RowsMemBaseField
import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevL
import Formalism.LocalRingCardinality.SpanPowerMembership.NZColA
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExplicitParameters
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevChOfLevelPrime
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Jutila
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.QuadraticHeckeZeroEstimates
import Development.AutomorphicArithmetic.ThickFrames.ThickFrame2Large
import Development.AutomorphicArithmetic.CharacterBoxes.RealSplit
import Formalism.GL3MeanSquares.HookFormulaTorsion.GlobalBoundRefinements
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogFactorialEqSumVonMangoldtMulDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogDerivSeriesOfExplicit
import Development.AutomorphicArithmetic.MeanSquareBounds.Thin
import Development.AutomorphicArithmetic.MeanSquareBounds.SmallZeros
import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRefill
import Development.AutomorphicArithmetic.ThickFrames.topsBase
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.XLeZBaseOfPowLeN
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
import Development.AbelianVarietyTheory.Proofs.HeightProofs.JointQOfSmallField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HostSzOfSizes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsRayIntermediateField
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardFrameOfDiagonalStages
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily

noncomputable section

namespace GlobalTheory.Diag.PG.Model0

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem two_le_rd {R : Ranks} (H : Host R) : 2 ≤ H.rdE := UpperTheory.Ram.Rd.two_le_rdE H

theorem logrd_le {D : D7} (L : SizeData₂ D) (SzN : SizeN L) (SzQ : SizeQD L) (h2 : 2 ≤ XX L) (h3 : 5 / szTh L ≤ XX L) :
    Real.log D.host.rdE ≤ L.sc.x ^ (L.sc.eps / 2) := by
  obtain ⟨-, -, q2, -, d2, -⟩ := SzQ
  have a := UpperTheory.Ram.Rd.log_rdE_le D.host
  have b := logn_le L SzN
  have c := logx_le L
  have e21 : L.sc.x ^ (L.sc.eps / 5 + szTh L) = XX L ^ 21 := by
    rw [← xpow_nat L 21]; congr 1; unfold szTh; push_cast; ring
  have e50 : L.sc.x ^ (L.sc.eps / 2) = XX L ^ 50 := by
    rw [← xpow_nat L 50]; congr 1; unfold szTh; push_cast; ring
  rw [e21] at q2 d2
  rw [e50]
  have hth := th_pos L
  have k1 : 5 * (XX L / szTh L) ≤ XX L ^ 2 := by
    have : 5 * (XX L / szTh L) = 5 / szTh L * XX L := by ring
    rw [this, sq]; exact mul_le_mul_of_nonneg_right h3 (by linarith)
  have k0 : 0 ≤ XX L / szTh L := by positivity
  have k2 : XX L ^ 2 ≤ XX L ^ 21 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have k3 : 1 ≤ XX L ^ 21 := one_le_pow₀ (by linarith)
  have k4 : 4 ≤ XX L ^ 29 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) h2 29)
  have k5 : XX L ^ 50 = XX L ^ 21 * XX L ^ 29 := by ring
  nlinarith

theorem globalRows_of_sizeData {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (Sz : SizesAt L) (h2 : 2 ≤ XX L)
    (h3 : 5 / szTh L ≤ XX L) (CD : ℝ) (h0 : 0 < CD) (hC : CD ≤ P.CCount) :
    Glob0 D L.sc.x L.sc.eps CD (P.CYL + 1) := by
  obtain ⟨SzN, SzM, SzK, SzKR, -, -, SzQ, -, -, -, -, -, -, -, SzNo, -, SzD, -⟩ := Sz
  have hx1 := L.sc.one_lt_alt
  have hx : 0 < L.sc.x := by linarith
  have he := L.sc.eps_pos
  have he' := L.sc.eps_lt
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hS := Sc_eq' L
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, Real.log_le_log (by norm_num) (two_le_rd _), logrd_le L SzN SzQ h2 h3, count_power_le_discriminant L P CD h0 hC, ?_⟩,
    type_prime_size_bounds L P, fun τ j h => ?_, fun τ i => ?_, fun τ ht => ?_, two_le_rd _⟩
  · have a := SzM.1
    rw [sqrt_xd L, ← Real.rpow_add hx] at a
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_) a
    unfold szTh; linarith
  · exact_mod_cast hyp3 L SzN SzM
  · exact_mod_cast D.R.f_le_k
  · have a := SzKR.1
    have b : L.sc.x ^ (L.sc.eps / 2) ≤ L.sc.x ^ L.sc.eps := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have c : 1 ≤ L.sc.x ^ szTh L := (one_lt_XX L).le
    have e : L.sc.L = L.sc.x ^ L.sc.eps := rfl
    rw [e] at a
    refine le_trans ?_ a
    calc _ = 1 * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.x ^ L.sc.eps * L.sc.x ^ (L.sc.eps / 2) := by ring
      _ ≤ _ := by gcongr
  · refine SzK.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_)
    unfold szTh; linarith
  · have b : L.sc.x ^ (L.sc.eps / 4) ≤ L.sc.x ^ (L.sc.eps / 2) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have c : 0 ≤ L.sc.x ^ (L.sc.eps / 4) := by positivity
    linarith [P.logDel]
  · exact le_trans SzNo.2.2.1 (P.nodes_gap τ j h).1
  · rw [← hS]; exact L.cloud_v τ i
  · have hn : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces := fun h => ht ((isTop_iff τ).2 h)
    have a := (L.cloud_gap τ (by omega) hn).1
    have b := P.cloud_place_bound τ (by omega) hn
    have c := P.uk_extreme τ (by omega) hn
    push_cast at a b
    unfold uFirst vFirst uLast vLast
    refine ⟨by linarith, by linarith, ?_⟩
    rw [c]; push_cast; ring

end GlobalTheory.Diag.PG.Model0

end
