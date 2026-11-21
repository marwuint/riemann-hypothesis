import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyStatementOfAbsAndVandermonde
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumNormSqOrthonormalLeHilbertSchmidt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCLC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExpQuarterMulExpQuarterLeTwo
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.AutomorphicFormsFiniteUnitaryIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Formalism.PeriodIntegrals.BesselMapUniq
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNml
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
import Formalism.LocalRingCardinality.DataTies
import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedUniformRotatedOfExpansion
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThmBChain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdSubEqProdFactorial
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowColumnShapeOfWindowDataWidthGeOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThresholdCriticalLevelLowerBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmplitudeBoundsAtParamsOfAdmittedBounds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFormalDegreeEqVandermondeOfSizes
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeRatioEqVandermondeRatioAlongLine
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmpleThetaWideRangeLargeConstants
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PtDlAtRecord
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealPlaceAmplitudeNormLeConstDivFormalDegree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsAllAtRecordGap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurAtRecordGap

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AmpRecordGap

theorem isHCParam_u (R : Ranks) (P : HCParam R) : Formalism.QuantumDeterminants.IsHCParam (fun i => ((P.u i : ℚ) : ℝ)) := by
  have hk := R.m_add_three_le_k
  obtain ⟨c, hc⟩ := R.k_even
  have step : ∀ (i : ℕ) (h : i + 1 < R.k), P.u ⟨i + 1, h⟩ < P.u ⟨i, by omega⟩ := fun i h =>
    lt_trans (P.v_gt_u ⟨i, by omega⟩) (P.u_gt_v ⟨i, by omega⟩)
  refine ⟨?_, fun a => ?_⟩
  · have key : ∀ (d i : ℕ) (h : i + d + 1 < R.k), P.u ⟨i + d + 1, h⟩ < P.u ⟨i, by omega⟩ := by
      intro d
      induction d with
      | zero => intro i h; exact step i h
      | succ d ih => intro i h; exact lt_trans (step (i + d + 1) h) (ih i (by omega))
    intro i j hij
    have hlt : i.val < j.val := hij
    have := key (j.val - i.val - 1) i.val (by omega)
    have e : P.u ⟨i.val + (j.val - i.val - 1) + 1, by omega⟩ = P.u j := congrArg P.u (Fin.ext (by simp; omega))
    rw [e] at this
    beta_reduce
    exact_mod_cast this
  · obtain ⟨z, hz⟩ := P.u_half a
    refine ⟨z - c + 1, ?_⟩
    simp only
    rw [hz, hc]; push_cast; ring

theorem isHCParam_uS (D : D7) (w : D.what₂.Word) (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.IsHCParam (uS D w τ) :=
  isHCParam_u D.R (D.hcW w τ)

theorem weyl_at (D : D7) : VanishingOnXAndXPlusBranching.adm12 D := by
  intro τ w H _ _ z π hπ
  obtain ⟨g, -, hg⟩ := hπ
  exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS D w τ)).1 H _ hg

theorem ampOn_singleton : ∀ c : ℝ, AmpOn {c} := by
  intro c Cg cb Cu cT CT hcb _
  obtain ⟨CPT, hPT⟩ := _root_.GlobalTheory.Core.Deg.ptWide_at_record_gap Cg cb Cu cT CT c
  obtain ⟨CDl, hDl⟩ := GlobalTheory.CoreDlGap.ptDl_at_record Cg cb Cu cT CT c
  obtain ⟨Ca, hCa, hAbs⟩ := GlobalTheory.AbsRecGap.abs_all_at_record_gap Cg cb Cu cT CT c
  obtain ⟨CS, tS, hS⟩ := GlobalTheory.Amp.schur_at_record_gap Cg cb Cu cT CT c
  obtain ⟨tL, hL⟩ := _root_.GlobalTheory.CritLevelSize.tcritLow_sizes cb Cu hcb
  obtain ⟨tV, hV⟩ := _root_.GlobalTheory.Core.Deg.CritVand.vv_eq_vand_of_sizes
  obtain ⟨C, C2, Ch, hC, hCh, H⟩ := _root_.GlobalTheory.ampAt_record_of_inputs Cg CPT CDl 1 Ca CS zero_le_one hCa
  refine ⟨C, C2, Ch, hC, hCh, fun Cpr δ hδ => ?_⟩
  obtain ⟨t0, H0⟩ := H Cpr δ hδ
  obtain ⟨t1, h1⟩ := hPT (max Cpr 0)
  obtain ⟨t2, h2⟩ := hDl (max Cpr 0)
  obtain ⟨t3, h3⟩ := _root_.GlobalTheory.AmpRec.exists_threshold_adm9_of_ties Cg cb Cu cT CT c (max Cpr 0)
  obtain ⟨t4, h4⟩ := hAbs (max Cpr 0)
  obtain ⟨t5, h5⟩ := _root_.GlobalTheory.DegLine.deg_VandLine_of_gap (max Cpr 0)
  refine ⟨max t0 (max t1 (max t2 (max t3 (max t4 (max tS (max tL (max tV t5))))))),
    fun C0 hC0 C' Cl hC' hCl D large₂ hG hT _ hTF => ?_⟩
  obtain rfl : C0 = c := hC0
  simp only [max_le_iff] at hC' hCl
  obtain ⟨a0, a1, a2, a3, a4, aS, -, aV, a5⟩ := hC'
  obtain ⟨b0, b1, b2, b3, b4, bS, bL, bV, b5⟩ := hCl
  have hLow : VanishingOnXAndXPlusBranching.adm5 D large₂ C' Cl Cg cb Cu cT CT C0 := fun h0 =>
    hL D large₂ C' Cl Cg cT CT C0 bL
      (hV D large₂ C' Cl Cg cb Cu cT CT aV bV hT h0.1 (_root_.GlobalTheory.Core.Deg.rowColumnShape_of_windowData_width_ge_one D C0 h0.2.2 h0.2.1)) h0
  exact H0 D large₂ C' Cl cb Cu cT CT C0 a0 b0 hG
    (h1 D large₂ C' Cl a1 b1 hT hTF)
    (h2 D large₂ C' Cl a2 b2 hT)
    hLow
    (h3 D large₂ C' Cl a3 b3 hT)
    (Formalism.MainNotions.BridgeLemma₂.degree_ratio_one_of_vandermonde _ _ _ _ _ _ _ _ _ _ _ _
      (h5 D large₂ C' Cl Cg cb Cu cT CT C0 1 a5 b5 hT))
    (h4 D large₂ C' Cl a4 b4)
    (hS D large₂ C' Cl aS bS hT)
    (weyl_at D)

end GlobalTheory.AmpRecordGap
