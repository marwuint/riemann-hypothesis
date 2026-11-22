import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IterationAndLinearityCuspidal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsExpansionZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowRealIteratedIntegralEqConstMulFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellSumRelationsPassToIntegralsProof
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodGroupsSplitRealFiniteLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedIntegrandBiInvariantLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrandSupportedOnCellsLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCellValueOfStepsLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SingleCosetOffTwistPlacesLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellMassesAgainstLevelVolumesLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodReductionToFockVectorsLargeDepth
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedIterateEventuallyLarge

section
open GlobalTheory.RowClaim GlobalTheory.RowVal GlobalTheory.RowReal
namespace GlobalTheory.RowUnfLast
theorem twisted_theta_integral_unfolding : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → SumOKK → StepUnfold := fun p c s =>
  have rel := _root_.GlobalTheory.RowRealInt.unfold_of_steps
  have hcv := _root_.GlobalTheory.RowVal.cellVan_holds
  have grp := _root_.GlobalTheory.RowGrpSplit.grpAt_big
  have it := _root_.GlobalTheory.T.twisted_iterate_chain
  have inv := _root_.GlobalTheory.RowInv.main
  have flat := GlobalTheory.RowFlatAsm.flatAt_big
  have supp := _root_.GlobalTheory.RowVal.big_suppOn_of_flat
  have rep := _root_.GlobalTheory.RowRep.rep_at
  have val := _root_.GlobalTheory.RowVal.valAt_big
  have off := _root_.GlobalTheory.RowOneCos.offAt_big
  have tens := _root_.GlobalTheory.RowVal.tensAt_big
  have vol := _root_.GlobalTheory.RowVal.volAt_big
  have wt := _root_.GlobalTheory.RowWt.wtAt_big
  have fock := _root_.GlobalTheory.FockRed.fockAt_big
  have bas := _root_.GlobalTheory.RowBasic.basicAt
  have one := _root_.GlobalTheory.RowVal.oneAt
  have rl := GlobalTheory.RowReal.realLine
  big_mono (fun ch ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rel, grp⟩, it⟩, inv⟩, ⟨e, fl⟩⟩, supp⟩, rep⟩, val⟩, off⟩, tens⟩, vol⟩, wt⟩, fock⟩, bas⟩, one⟩, rl⟩, s⟩ =>
    rel grp it.1 it.2 inv ⟨e, supp e fl off inv tens bas, rep e, val e fl tens vol (wt e) fock bas one s⟩ rl s)
  (((((((((((((((((rel hcv).and grp).and (it p c)).and inv).and flat).and supp).and rep).and val).and off).and tens).and vol).and wt).and fock).and bas).and one).and rl).and s)
end GlobalTheory.RowUnfLast
end

section
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_integral_unfolds : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → SumOKK → StepUnfold := GlobalTheory.RowUnfLast.twisted_theta_integral_unfolding
end
