import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevSIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionEqOneOffSplitPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjStabilizesFramedLatticeIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionOfMemLevelZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.TopLevQ.red_eq_zero_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (t h : GA D V) (N M : Matrix (Fin V.rank) (Fin V.rank) k), GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) V t β N → (Formalism.L2.Theta.mt V h).map q.pr * N = N * M → Lev.finE V (t⁻¹ * h * t) ∈ Formalism.L2.DIV.St β → ∀ i j, ((Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j = 0 ↔ ValuativeRel.valuation k (M i j) < 1) := by
  intro D k _ _ _ _ q PP hPP V β t h N M hN hM hSt i j
  constructor
  · intro h0
    have := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β t h N M hN hM hSt i j 0 (by rw [h0, map_zero])
    have e0 : (GlobalTheory.LocMod.ofSplit q).pr ((0 : 𝓞 D.host.E) : D.host.E) = 0 := by
      show (GlobalTheory.LocMod.ofSplit q).π ((incA D) ((0 : 𝓞 D.host.E) : D.host.E)) = 0
      rw [show ((0 : 𝓞 D.host.E) : D.host.E) = 0 from rfl, map_zero, map_zero]
    rwa [e0, sub_zero] at this
  · intro hv
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective ((Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j)
    have h1 := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β t h N M hN hM hSt i j z hz
    have h2 : ValuativeRel.valuation k ((GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E)) < 1 := by
      have e : (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E) = M i j - (M i j - (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E)) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv h1)
    obtain ⟨π', hπ, hred, -⟩ := _root_.GlobalTheory.FinPl.SplitPt.exists_lift_isRed D k q PP hPP
    have h6 : (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E) = (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) := (hπ _).symm
    rw [h6, ← hred.ker, Formalism.L2.DIV.resS_oToS] at h2
    rw [← hz, h2]

end
