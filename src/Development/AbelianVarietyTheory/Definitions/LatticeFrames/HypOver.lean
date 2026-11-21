import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RankConditionRankOneIffEqZero
import Formalism.SharpRestriction.FamCore
import Formalism.LocalRingCardinality.SpanPowerMembership
import Formalism.LocalRingCardinality.SpanPowerMembership.RowsMemBaseField
import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevM
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowQ
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeH
import Formalism.LocalRingCardinality.SpanPowerMembership.TrivialColumnsRamifiedTop
import Formalism.LocalRingCardinality.SpanPowerMembership.GPlacesExampleNatAct
import Formalism.CyclotomicNorms.StatementT
import Formalism.LocalRingCardinality.SpanPowerMembership.EntPlNonempty
import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

noncomputable section

namespace GlobalTheory.Core.RkFamModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ GlobalTheory.Core.Rk NumberField Module

theorem xu_pos (D : D7) (u : D.what₂.Word) : 0 < (D.mem u).A.Xu := by
  have h1 := (D.mem u).A.Dstar_pos
  have h2 : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  unfold ColumnsAtT.Xu
  positivity

theorem fk_pos (R : Ranks) : (0 : ℝ) < (R.f : ℝ) * R.k := by
  have := R.m_add_three_le_k
  have h1 : 0 < R.k := by omega
  have h2 : 0 < R.f := Nat.mul_pos two_pos R.ord_pos
  positivity

theorem log_tstar (D : D7) (u : D.what₂.Word) : Real.log (D.mem u).A.Tstar =
    Real.log (D.mem u).A.Xu - 2 / ((D.R.f : ℝ) * D.R.k) * Real.log (D.mem u).A.GamP := by
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  unfold ColumnsAtT.Tstar
  rw [Real.log_mul (xu_pos D u).ne' (Real.rpow_pos_of_pos hG _).ne', Real.log_rpow hG]
  ring

theorem log_T_lt (D : D7) (u : D.what₂.Word) :
    Real.log ((D.mem u).A.T : ℝ) < Real.log (D.mem u).A.Xu + 1 / ((D.R.f : ℝ) * D.R.k) := by
  have hT : (0 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hf := fk_pos D.R
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hs : 0 < (D.mem u).A.Tstar := mul_pos (xu_pos D u) (Real.rpow_pos_of_pos hG _)
  have h1 := Real.log_le_log hT (D.T_win u).2
  rw [Real.log_mul (by positivity) hs.ne', log_tstar] at h1
  have h2 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((D.R.f : ℝ) * D.R.k))
  have h3 : 0 < 2 / ((D.R.f : ℝ) * D.R.k) * Real.log (D.mem u).A.GamP :=
    mul_pos (by positivity) (Real.log_pos (D.mem u).A.one_lt_gammaP)
  linarith

end GlobalTheory.Core.RkFamModel

namespace GlobalTheory.Core.RkOverModel

end GlobalTheory.Core.RkOverModel

end
