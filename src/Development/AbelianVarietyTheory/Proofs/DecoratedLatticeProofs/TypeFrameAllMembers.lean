import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizesEqCount
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassNumberAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstTypePrimeLargeOfRecord
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegreeHypothesisAllMembers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataNonvanishingAllMembers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColumnDimensionWindowThreeOfColumnCount
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFormalDegreeEqVandermondeOfSizes

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.MemberFrame

open Formalism.MainNotions.S in

theorem member_frame_of_standing_hypotheses_window_three {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Formalism.BasicNotions.Ties D) (hR : LocalBesselAndTopKernel.FamilyMidVolume D)
    (h : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT 3) (h29 : 29 ≤ C') (h40 : 40 ≤ Cl)
    (hCu : Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1) : Formalism.L2.SG.RowsConc.TFrameAt D := by
  have hH := h.1
  have hyp : LocalBesselAndTopKernel.hyp D large₂ 3 C' Cl Cg cb Cu cT CT := ⟨h.2.1, h.1, h.2.2⟩
  have hL := Formalism.MainNotions.BridgeLemma.one_le_scale_log large₂
  have hG := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH (by linarith) h29
  have hVV : ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ)) := by
    intro τ
    have hgap := Formalism.L2.SG.Pf.WuBL.gapAtLeast_of D.R (D.hc τ) (hG.2 τ)
    have hds := GlobalTheory.dsig_eq_fdegHC_of_gap D hT τ _ (Formalism.L2.Col.lamSH_isHCParam (D.hc τ)) hgap
      (GlobalTheory.Core.Deg.CritVand.thrE_add_one_lt D.R hG.1)
    have hanti := Formalism.MainNotions.BridgeLemma.szh_anti hH τ
    have hSF : (0 : ℝ) < ∏ i ∈ Finset.range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
      Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
    unfold VV
    rw [hds, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← dimS_eq]
    field_simp
  have hg : LocalBesselAndTopKernel.MidVolumeChain D large₂ (1 / 3) 0 := by
    intro τ
    rw [hVV τ]
    have h0 : 0 ≤ vand (lamSH D.R (D.hc τ)) := Formalism.MainNotions.BridgeLemma.szh_vand_nonneg _ (Formalism.MainNotions.BridgeLemma.szh_anti hH τ)
    have h1 : 1 ≤ Real.exp ((0 : ℝ) * D.R.k * D.R.m * large₂.sc.L) := Real.one_le_exp (by simp)
    constructor
    · nlinarith
    · nlinarith
  have hD : UnitaryVolumeMass.cTvD D 1 :=
    Formalism.MainNotions.BridgeLemma.critical_level_lower_bound (C3' := 1) h40 (by norm_num) le_rfl hyp hg
  have hA : UnitaryVolumeMass.cTvA D :=
    Formalism.MainNotions.BridgeLemma.degree_ratio_product_formula D (Formalism.MainNotions.BridgeLemma.stMassRatio_of_siegel GlobalTheory.Mass.siegelMassRatio_holds D) hR
      (Formalism.MainNotions.BridgeLemma.sza_spl_of_data h.2.1) (Formalism.MainNotions.BridgeLemma.sza_g_ge hH)
  have F := Formalism.MainNotions.BridgeLemma.tfFacts_of h
  have hm : 2 * (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; norm_num; exact_mod_cast this
  have hm40 : (40 : ℝ) ≤ D.R.m := le_trans h40 hH.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk : 3 * Real.exp 8 ≤ (D.R.k : ℝ) := by
    have e8 : Real.exp 8 ≤ 3 ^ 8 := by
      have h3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
      calc Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 3 ^ 8 := pow_le_pow_left₀ (Real.exp_pos _).le h3 8
    have hf := Formalism.MainNotions.BridgeLemma.two_le_degree_bis D
    have h5 : (40 : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hm40 5
    have hk' : 29 * (40 : ℝ) ^ 5 * 2 * 1 ≤ C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      have : 0 ≤ C' := by linarith
      gcongr
    have := F.hk
    linarith
  exact fun w => F.tframe (by linarith) hm hCu hA hD hk w

theorem three_L_le {s : Scale} {R : Ranks} (h : RankVal s R) (he : s.eps < 1 / 52) (hx : 256 ≤ s.x) :
    3 * s.L ≤ (R.m : ℝ) - 1 := by
  have h1 : Real.sqrt (s.x * s.delta1) ≤ (R.m : ℝ) := h.2.1.1
  have hx0 : 0 < s.x := by linarith
  have hx1 : 1 ≤ s.x := by linarith
  have he0 := s.eps_pos
  have hL : 1 ≤ s.x ^ s.eps := Real.one_le_rpow hx1 he0.le
  have h4 : (4 : ℝ) ≤ s.x ^ ((1 : ℝ) / 4) := by
    calc (4 : ℝ) = ((4 : ℝ) ^ (4 : ℕ)) ^ (((4 : ℕ) : ℝ))⁻¹ := (Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
      _ = (256 : ℝ) ^ ((1 : ℝ) / 4) := by norm_num
      _ ≤ s.x ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have hs : s.x ^ s.eps * s.x ^ ((1 : ℝ) / 4) ≤ Real.sqrt (s.x * s.delta1) := by
    have e : s.x * s.delta1 = s.x ^ (1 + -(s.eps / 8)) := by
      unfold Scale.delta1
      rw [Real.rpow_add hx0, Real.rpow_one]
    rw [e, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  show 3 * s.x ^ s.eps ≤ (R.m : ℝ) - 1
  nlinarith

theorem Dstar_eq_mass (K : Ctx) (X : Stages) (hO : K.Over X.B.toPre)
    (hd : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)) :
    X.toD7.what₂.Dstar = StandardLattice.massI X.toD7 X.toD7.R.r * StandardLattice.idxSig X.toD7 (X.toD7.host.g 0) (X.toD7.host.g 1) *
      ∏ τ, X.toD7.dsig τ := by
  have e : X.toD7.what₂.Dstar = X.B.Dstar := (X.toD7.Dstar_eq X.toD7.u₀).symm.trans (X.C.A_Dstar _)
  rw [e, hO.sizes.2]
  unfold DsPre
  congr 1
  exact Finset.prod_congr rfl fun τ _ => (hd τ).symm

theorem admissible_ranks_of_mass_formula (D : D7) (Lv : LevelData D) (C : Formalism.L2.Forms.ColsTiedSym D)
    (hD : D.what₂.Dstar = StandardLattice.massI D D.R.r * StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) * ∏ τ, D.dsig τ) :
    LocalBesselAndTopKernel.FamilyMidVolume D := by
  have h4 := Formalism.MainNotions.StandardLattice.HarishChandraReduction.rankFormula_of_classNumber D Lv (GlobalTheory.ColClassNumber.classNumber_all D Lv)
  intro V _ _ _ _ h L _
  refine ⟨fun hL u => ?_, fun hL => ?_⟩
  · have e := h4 (GlobalTheory.first_type_prime_large_of_record D) (Formalism.MainNotions.Ext.Lw.splitsF_g_all D) u
      (Formalism.MainNotions.Ext.Lw.splitsF_T_all D u) (Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u)
    have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.k := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.k)
    rw [em, ← Formalism.MainNotions.J.idxColTie_holds D]
    exact e
  · have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.r := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.r)
    rw [em, ← Formalism.MainNotions.J.idxRowTie_holds D, hD]

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL)

end GlobalTheory.Fam.MemberFrame

end
