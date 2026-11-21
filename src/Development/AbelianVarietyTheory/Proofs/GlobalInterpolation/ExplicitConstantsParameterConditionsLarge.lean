import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowAndImp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowPrimesConductor
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceRankKLowerUpperBounds
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RankRowsOfCrudeBounds
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogfSqLeRS
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaBounds
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaLeW
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTopsBandBottoms
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCloudLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowWindowLength
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowExact
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfLeAbsNodeSubMid
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceRowWeightRatioAndLastCloudLeTwiceF
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowThinSizeGe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCloudUnitLower
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNodeGap
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowGapFunFN
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSigGaps
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RbSNumeric
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLStarStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCardWordsLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTypePrimes
import Development.AutomorphicArithmetic.WeightCongruences.IffNum

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem Std.parConsts_pos {C : FC} (hC : Std C) : ∀ c ∈ C.P.list, 0 < c := by
  obtain ⟨hF, -, h1, h2, h3, h4, h5, -, -, -, -, h6, h7, -, hM, hL⟩ := hC
  obtain ⟨-, -, -, -, -, -, -, h8, -, -⟩ := hF
  simp only [FC.cLast, FC.cMid, List.forall_mem_cons] at hM hL
  obtain ⟨hCF, -⟩ := hM
  obtain ⟨a1, a2, a3, a4, a5, -, a6, a7, a8, a9, a10, a11, a12, a13, a14, -⟩ := hL
  have a4' : 0 < C.P.cLL := inv_pos.mp (lt_of_lt_of_le one_pos a4)
  simp only [PC.list, List.forall_mem_cons]
  refine ⟨?_, ?_, ?_, a4', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩ <;>
    linarith

theorem explicitConstants_parameterConditions_large :
    SzRow (fun C D L => HostArith D.host → ∃ P : ParameterChoice' D L, parConsts P = C.PK ∧ P.CnW = C.P.CnW) := by
  refine SzRow.imp (
    SzRow.and _root_.GlobalTheory.EX.szRow_primes_conductor <|
    SzRow.and GlobalTheory.EX.explicitChoice_rankK_lower_upper_bounds <|
    SzRow.and GlobalTheory.EX.szRow_rank_lower_bounds <|
    SzRow.and GlobalTheory.EX.szRow_logf <|
    SzRow.and _root_.GlobalTheory.EX.szRow_eta_bounds <|
    SzRow.and _root_.GlobalTheory.EX.szRow_eta_le_w <|
    SzRow.and _root_.GlobalTheory.EX.szRow_tops_band_bottoms <|
    SzRow.and GlobalTheory.EX.szRow_cloud_le <|
    SzRow.and GlobalTheory.EX.szRow_windowLength <|
    SzRow.and GlobalTheory.EX.szRow_exact <|
    SzRow.and GlobalTheory.EX.szRow_lowsFar <|
    SzRow.and _root_.GlobalTheory.EX.szRow_size_ratio <|
    SzRow.and GlobalTheory.EX.szRow_thinSize_ge <|
    SzRow.and _root_.GlobalTheory.EX.szRow_cloudUnit_lower <|
    SzRow.and _root_.GlobalTheory.EX.szRow_nodeGap <|
    SzRow.and _root_.GlobalTheory.EX.szRow_gap_fun_fN <|
    SzRow.and GlobalTheory.EX.szRow_sig_gaps <|
    SzRow.and GlobalTheory.EX.szRow_rbS <|
    SzRow.and GlobalTheory.T.sizes_b_add_Sc_add_etaSz_add_div_lt_lStar <|
    SzRow.and GlobalTheory.EX.szRow_card_words_le <|
    _root_.GlobalTheory.EX.szRow_typePrimes) ?_
  intro C cD ch D L hC _ h hA
  obtain ⟨⟨h_qd_pow, h_logq_ge, h_dlogL1_le, h_condE_le, h_pde_log⟩,
    ⟨h_k_low, h_k_up, h_R0_ge⟩,
    ⟨h_k_ge_m2L, h_k_ge_mx, h_klogk, h_flogk⟩,
    ⟨h_logf_le, h_log2f_le, h_loglogb, h_nW_ge⟩,
    ⟨h_eta_le, h_logeta, h_t_le_eta, h_teta, h_mteta⟩,
    ⟨h_mSeta, h_Neta, h_eta2, h_kS_le⟩,
    ⟨h_TT_card_le, h_rho_le, h_bT_le⟩,
    ⟨h_S_le, h_Del_le, h_logDel⟩,
    ⟨h_Lw_j, h_Lw_le, h_j0_le⟩,
    ⟨h_top_b1, h_cloud_le2, h_uk_extreme, h_em_win, h_nodes_gap, h_e_centred, h_e_parity, h_etaF_eq, h_pde_mod, h_pde_ne, h_ccK_log, h_ccK_le⟩,
    h_lows_far,
    ⟨h_X''_ratio, h_bm_le⟩,
    h_w''_ge,
    ⟨h_Del_ge, h_Del_count⟩,
    h_h0_ge,
    ⟨h_h0_fun, h_h0_fN⟩,
    h_sig_gaps,
    h_rbS,
    ⟨h_lstar1, h_lstar2⟩,
    h_words_le,
    h_g_Y⟩ := h
  have hp := hC.parConsts_pos
  simp only [PC.list, List.forall_mem_cons] at hp
  obtain ⟨p_CkLow, p_Ck6, p_CfL, p_cLL, p_CnW, p_Crho, p_CDelG, p_CLw, p_Cj0, p_Cw, p_cw, p_CDel, p_CCount, p_Ch0r, p_Ch0k, p_Ch0N, p_Cgap, p_CetaF, p_CY, p_CYL, p_Cpde, p_CccK, p_CF, -⟩ := hp
  exact ⟨
    { CkLow := C.P.CkLow, CkLow_pos := p_CkLow
      Ck6 := C.P.Ck6, Ck6_pos := p_Ck6
      CfL := C.P.CfL, CfL_pos := p_CfL
      cLL := C.P.cLL, cLL_pos := p_cLL
      CnW := C.P.CnW, CnW_pos := p_CnW
      Crho := C.P.Crho, Crho_pos := p_Crho
      CDelG := C.P.CDelG, CDelG_pos := p_CDelG
      CLw := C.P.CLw, CLw_pos := p_CLw
      Cj0 := C.P.Cj0, Cj0_pos := p_Cj0
      Cw := C.P.Cw, Cw_pos := p_Cw
      cw := C.P.cw, cw_pos := p_cw
      CDel := C.P.CDel, CDel_pos := p_CDel
      CCount := C.P.CCount, CCount_pos := p_CCount
      Ch0r := C.P.Ch0r, Ch0r_pos := p_Ch0r
      Ch0k := C.P.Ch0k, Ch0k_pos := p_Ch0k
      Ch0N := C.P.Ch0N, Ch0N_pos := p_Ch0N
      Cgap := C.P.Cgap, Cgap_pos := p_Cgap
      CetaF := C.P.CetaF, CetaF_pos := p_CetaF
      CY := C.P.CY, CY_pos := p_CY
      CYL := C.P.CYL, CYL_pos := p_CYL
      Cpde := C.P.Cpde, Cpde_pos := p_Cpde
      CccK := C.P.CccK, CccK_pos := p_CccK
      CF := C.P.CF, CF_pos := p_CF
      qd_pow := h_qd_pow
      logq_ge := h_logq_ge
      logDerivative_le_power := h_dlogL1_le
      condE_le := h_condE_le
      pde_log := h_pde_log
      k_low := h_k_low
      k_up := h_k_up
      radius_ge_sqrt_ratio := h_R0_ge
      k_ge_m2L := h_k_ge_m2L
      k_ge_mx := h_k_ge_mx
      klogk := h_klogk
      flogk := h_flogk
      logf_le := h_logf_le
      log_sq_conductor_le := h_log2f_le
      loglogb := h_loglogb
      nW_ge := h_nW_ge
      eta_le := h_eta_le
      logeta := h_logeta
      t_le_eta := h_t_le_eta
      teta := h_teta
      mteta := h_mteta
      mSeta := h_mSeta
      Neta := h_Neta
      eta2 := h_eta2
      kS_le := h_kS_le
      TT_card_le := h_TT_card_le
      rho_le := h_rho_le
      bT_le := h_bT_le
      S_le := h_S_le
      Del_le := h_Del_le
      logDel := h_logDel
      Lw_j := h_Lw_j
      Lw_le := h_Lw_le
      jetIndex_le_log := h_j0_le
      topPlace_first_bound := h_top_b1
      cloud_place_bound := h_cloud_le2
      uk_extreme := h_uk_extreme
      em_win := h_em_win
      nodes_gap := h_nodes_gap
      e_centred := h_e_centred
      e_mu := fun j => (h_e_parity j).num
      etaF_eq := h_etaF_eq
      pde_mod := h_pde_mod
      pde_ne := h_pde_ne
      ccK_log := h_ccK_log
      ccK_le := h_ccK_le
      lows_far := h_lows_far
      X''_ratio := h_X''_ratio
      bm_le := h_bm_le
      w''_ge := h_w''_ge
      Del_ge := h_Del_ge
      Del_count := h_Del_count
      h0_ge := h_h0_ge
      heightBound_ge_rank_cubic := h_h0_fun
      heightBound_ge_degree_power := h_h0_fN
      sig_gaps := h_sig_gaps
      rbS := h_rbS
      lstar1 := h_lstar1
      lstar2 := h_lstar2
      words_le := h_words_le
      g_Y := h_g_Y
      g_norm := hA.1
      g_mod := hA.2.1
      pde_split := hA.2.2.1
      level_split := hA.2.2.2 }, rfl, rfl⟩

end GlobalTheory.EX
