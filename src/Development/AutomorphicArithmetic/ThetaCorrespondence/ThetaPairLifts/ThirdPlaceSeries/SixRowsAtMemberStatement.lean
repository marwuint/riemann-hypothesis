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
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixRowsAtMember

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_entries_tie_and_level_valuations_at_built : ∀ (𝒮 : Slots) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.ReferenceChainEvaluationAtBundlePoints S Lk) ∧ (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.TwistedPointAtBundlePoints S Lk) ∧ (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.PeriodAtZeroAtBundlePoints S Lk) ∧ (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.TwistedPeriodAtBundlePoints S Lk) ∧ (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.Row_tie S Lk) ∧ (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints S Lk) := by
  first | exact @_root_.GlobalTheory.Fc.six_rows_at_member_alt | exact _root_.GlobalTheory.Fc.six_rows_at_member_alt | (intros; apply _root_.GlobalTheory.Fc.six_rows_at_member_alt <;> assumption)
end
