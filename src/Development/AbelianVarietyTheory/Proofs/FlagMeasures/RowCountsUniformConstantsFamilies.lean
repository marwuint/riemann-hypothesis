import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeSizeZ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivIntegral
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CntClLeEncardMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeProdReal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountPrimitiveSublatticesOverGenus
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveCorankOneSublatticesBound
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleFamilyOfSteps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsRawMassAndGenusMass
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfLiftNumberGenus

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.RowCounts

theorem uniform_counts : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ c3 cH cS c4 thr : ℝ,
    ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm →
    (∀ C ≥ c3, (OwnEv Fm fun C' Cl x i => ∀ u u',
      VanishingOnXAndXPlus.adm20 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A 3 C)) ∧
    (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.HerrCocycleExtensionClass (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A cH) ∧
    (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A cS) ∧
    (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.adm21 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A c4) := by
  intro hM Cg cb Cu cT CT C0 A
  obtain ⟨C1a, hC1⟩ := _root_.GlobalTheory.Mass.PrimMeanRow.main 1 one_pos
  obtain ⟨c3, hC3⟩ := GlobalTheory.LoopC.PairMean.main Cg cb Cu cT CT C0 A 3 (max C1a 0) (le_max_right _ _)
  obtain ⟨cH, -, hHH⟩ := GlobalTheory.GramHeight.height_bounds Cg cb Cu cT CT C0 A
  obtain ⟨cS, hSW⟩ := GlobalTheory.LoopC.GenericMean.main Cg cb Cu cT CT C0 A
  obtain ⟨c4, hC4⟩ := GlobalTheory.LoopC.Partner.partners_le Cg cb Cu cT CT C0 A
  refine ⟨c3, cH, cS, c4, 1, fun eps Fm _ hl => ⟨fun C hC => ⟨0, fun x _ i u u' => ?_⟩,
    ⟨0, fun x _ i u u' => ?_⟩, ⟨0, fun x _ i u u' => ?_⟩, ⟨0, fun x _ i u u' => ?_⟩⟩⟩
  · exact hC3 C hC _ _ u u' _ _ hl (_root_.GlobalTheory.Mass.RowsRawMass.main _ u)
      (hC1 _ (le_max_left _ _) _ _ u u' _ _ Cg cb Cu cT CT C0 A hl)
  · exact hHH _ _ u u' _ _ hl
  · exact hSW _ _ u u' _ _ hl
      (_root_.GlobalTheory.Mass.PrimMeanCorankOne.main _ _ u u' _ _ Cg cb Cu cT CT C0 A (Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified hM _))
  · exact hC4 _ _ u u' _ _ hl

end GlobalTheory.RowCounts
