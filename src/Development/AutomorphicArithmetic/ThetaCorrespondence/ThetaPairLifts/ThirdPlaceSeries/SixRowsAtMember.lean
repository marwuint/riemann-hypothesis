import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTwistCoresOverTrueColumns
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeColumnValuationsBundlePointsOverColumn
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelPrimeColumnValuationsAtBundlePoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReferencePeriodIntegralBundlePointsOfOverColumns
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPeriodsIntegralAtBundlePoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReferenceChainEvaluationBundlePointsOverColumnsA
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedChainEvaluationRationalIntegralBundlePoin
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealSideColumnsCompatibleBundlePointsOverColumns
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc
theorem six_rows_at_member_alt : ∀ (𝒮 : Slots) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.ReferenceChainEvaluationAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.TwistedPointAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.PeriodAtZeroAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.TwistedPeriodAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.Row_tie S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints S Lk) := by
  intro 𝒮 Lk
  have hC : OverCols (sAnd (IsGoodE 𝒮) fun _ _ _ _ _ => True) :=
    (_root_.GlobalTheory.Fc.Cv.overCols_goodE 𝒮 (fun _ _ _ _ _ => True)).2
  have hT : LargeBaseCondition KPx (IsBuiltE 𝒮) fun _ _ _ _ _ => True := largeBaseProperty_true
  exact ⟨⟨_, hT, _root_.GlobalTheory.Fc.PeriodEntriesOverColumns.referenceChainEvaluation_bundlePoints_overColumns _ hC _ Lk⟩, ⟨_, hT, _root_.GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPtTw_of_overCols _ hC _ Lk⟩,
    ⟨_, hT, _root_.GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPer0_of_overCols _ hC _ Lk⟩, ⟨_, hT, _root_.GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPerTw_of_overCols _ hC _ Lk⟩,
    ⟨_, hT, _root_.GlobalTheory.Fc.PeriodEntriesOverColumns.row_tie_of_overCols _ hC _ Lk⟩, ⟨_, hT, _root_.GlobalTheory.Fc.Cv.row_level_valuations _ hC _ Lk⟩⟩
end GlobalTheory.Fc
end
