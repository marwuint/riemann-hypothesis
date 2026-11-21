import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LinkSPos
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamShareOfFreeT
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamBigOfRamShare
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HdNumbers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagCorollary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeWindow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiveLeHalfKfk
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinrankKerPuLeHsDev
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdmissibleRanksAllMembers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegreeHypothesisAllMembers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataNonvanishingAllMembers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeFrameAllMembers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RankConditionAllMembers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LargeGapAllMembers

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop

open GlobalTheory.Core.Rk

theorem trueE_of_trueD {D : D7} (h : TrueD D) : TrueE D :=
  let ⟨B, X, I, l, Z, e, ⟨w⟩⟩ := h; ⟨B, X, I, l, Z, e, w, w.S.pin⟩

theorem puNZ_at (D : D7) (u : D.what₂.Word) (e δ : ℝ) (hS : DiagS D u e) (hR : RamBig D u δ) (hlt : e < 1 - δ)
    (hd : 0 < d0 D u) : ∃ φ : (D.mem u).A.Mram, D.s.Pu u ((D.s_Cu u).symm ⟨φ.1, φ.2.1⟩) ≠ 0 := by
  by_contra hne
  push_neg at hne
  let FF : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u :=
    (D.s_Cu u).symm.toLinearMap ∘ₗ Submodule.inclusion (inf_le_left : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0)
  have hFF : Function.Injective FF := (D.s_Cu u).symm.injective.comp (Submodule.inclusion_injective _)
  have hle : Module.finrank ℂ (D.mem u).A.Mram ≤
      Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)) := by
    let g : (D.mem u).A.Mram →ₗ[ℂ] LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH) :=
      FF.codRestrict _ (fun φ => by rw [LinearMap.mem_ker]; exact hne φ)
    exact LinearMap.finrank_le_finrank_of_injective (f := g) (fun x y h => hFF (congrArg Subtype.val h))
  have hk := finrank_ker_Pu_le_hsDev D u
  obtain ⟨-, hbig⟩ := hR
  have hU : (GlobalTheory.Core.Rk.dU D u : ℝ) ≤ (Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)) : ℝ) := by
    unfold GlobalTheory.Core.Rk.dU; exact_mod_cast hle
  have hd' : (0 : ℝ) < (d0 D u : ℝ) := by exact_mod_cast hd
  unfold DiagS at hS
  have : (1 - δ) * (d0 D u : ℝ) ≤ e * (d0 D u : ℝ) := by linarith
  have := le_of_mul_le_mul_right this hd'
  linarith

theorem puNZ_of_sDiag {D : D7} (large₂ : SizeData₂ D) {C C' Cl Cg cb Cu cT CT : ℝ} (hC : 1 ≤ C) (hCG : C + 1 ≤ large₂.CGam) (hD : TrueD D)
    (hH : GlobalTheory.Core.Rk.HD D large₂.sc.L C' Cl Cg cb Cu cT CT) (hmu : ∀ u, RankMu D u) (hS : ∀ u, SDiag D u large₂.sc.L C) : PuNZ D := by
  intro u
  obtain ⟨hm, hT, hd, -⟩ := hd_numbers D u _ C' Cl Cg cb Cu cT CT hH
  have hG : Real.log (D.mem u).A.GamP = large₂.CGam * mfL D large₂.sc.L := by rw [large₂.Gam_eq u]; unfold mfL; ring
  have hw : 1 + 2 * C * mfL D large₂.sc.L ≤ 2 * Real.log (D.mem u).A.GamP := by rw [hG]; nlinarith
  have hCm : 5 ≤ C * mfL D large₂.sc.L := by nlinarith
  have hdiag := diag_corollary.2.1 D u _ C (by linarith) (hS u) ((levelPrime_window D u).2.2 _ C (hmu u) hw)
  have hf : D.R.f ≠ 0 := by
    intro h0
    unfold mfL at hm
    rw [h0] at hm
    norm_num at hm
  have hR := ramBig_of_ramShare D u (ramShare_of_trueD D u hD) hd (by omega)
  have h2 := two_eDiag_lt D u _ C hCm hT
  have h0 : 0 ≤ eDiag D large₂.sc.L C := by unfold eDiag; positivity
  exact puNZ_at D u _ _ hdiag hR (by linarith) hd

theorem evP_cGam (J : ℝ → ℝ → ℝ) : EvP fun κ _ => J (κ.C.P.CYL + 1) κ.C.CTu ≤ κ.C.CGam :=
  ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ =>
    ⟨⟨0, fun _ => 0, fun l => J (l.getD 6 0 + 1) (l.getD 13 0), fun _ => 0⟩, fun C _ _ hL =>
      ⟨0, fun _ _ => ⟨0, fun _ _ _ => ⟨0, fun _ _ _ => hL.2.2.1 C.CGam (by simp [Formalism.MainNotions.Inhab.FC.cMid])⟩⟩⟩⟩⟩

end GlobalTheory.MiTop
