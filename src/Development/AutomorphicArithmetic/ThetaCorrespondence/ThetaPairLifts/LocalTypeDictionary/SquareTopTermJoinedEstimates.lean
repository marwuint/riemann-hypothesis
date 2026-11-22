import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfied
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaConjugateMeanLogAbsBoundOfTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomConstantOfTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistBaseTupleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistEveryTupleOfCmThetaHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankSumLeHalfRank
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.PolarizationScalarImPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaBoundVp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearCombinationLogBoundRealInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLValueUpperBoundPermutedWeightsOfFE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBigOfNonvanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareRatioValuationWithoutNormFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LValueRatioLowerBoundGauge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRankSumLeTwoMulTotalRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricValueHeightBoundOfDenominatorsMeans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatRepr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerOfThetaMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomConstantOfTheta
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.NormBigOfNonvanishing
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleExistenceOfTheta
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomThetaNeZeroOfInnerProductFormula
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TowerOfThetaMatching

section
namespace GlobalTheory.SqTop
theorem square_top_term_joined_estimates : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → GlobalTheory.SqTop.Refl → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SqTop.DenSum ∧ GlobalTheory.SqTop.ThbSt ∧ GlobalTheory.SqTop.OneSqSt ∧ GlobalTheory.SqTop.BotSmall ∧ GlobalTheory.SqTop.BotNe ∧ GlobalTheory.SqTop.FieldDat ∧ GlobalTheory.SqTop.TorEx ∧ GlobalTheory.SqTop.DenEx ∧ GlobalTheory.SqTop.BotEx ∧ GlobalTheory.SqTop.LNe ∧ GlobalTheory.SqTop.TriEx ∧ GlobalTheory.SqTop.Tower := by
  intro hHD hPr hFE hTD hTr hZD hRefl hTI hLM
  have hS := _root_.GlobalTheory.HeckeStrip.completedLBoundedInStrips
  have hInp := _root_.GlobalTheory.NormSum.inp_all
  have hF : FieldDat := GlobalTheory.SqTop.fieldDat
  have hL : LNe := GlobalTheory.SqTop.lNe_of_functionalEquation hFE hS hF
  have hLB : LBound := _root_.GlobalTheory.SqTop.lBound_of hFE hS hF
  have hTor : TorEx := GlobalTheory.ToricExist.torEx hTr hF hL
  have hBA : BetaArch := _root_.GlobalTheory.SqTop.betaArch_of_transport hTr hF hLB hTor
  have hDE : DenEx := GlobalTheory.DenExist.denEx hZD hF
  have hDS : DenSum := GlobalTheory.DenSumPf.denSum hZD hF
  have hThb : ThbSt := _root_.GlobalTheory.SqTop.thbSt_of_inputs hTD hF hTor hDE hDS hBA
  have hBS : BotSmall := GlobalTheory.SqTop.BotSmallProof.botSmall_holds
  have hBC : BotConst := _root_.GlobalTheory.T.botConst_of_theta_matching hPr hTI hLM hInp hBS hL
  have hBE : BotEx := GlobalTheory.T.bottomPairs_exist_baseTuple hInp
  have hBET : BotExT := GlobalTheory.T.bottomPairsExistEveryTuple_of_cmThetaHypotheses hInp
  have hNB : NormBig := _root_.GlobalTheory.T.normBig_of_lNe hPr hInp hL
  have hRL : RhoLow := _root_.GlobalTheory.RhoLowProof.rhoLow_holds hTD hF hTor
  have hTri : TriEx := _root_.GlobalTheory.T.triEx_of_howe_duality_real hHD hPr hTI hLM hL
  have hBN : BotNe := _root_.GlobalTheory.T.bottomTheta_nonvanishing hPr hTI hLM hInp hL hBS hNB hTri
  have hTw : Tower := _root_.GlobalTheory.T.tower_of_theta_matching_lNe hPr hTI hLM hL
  have hOne : OneSqSt := GlobalTheory.T.square_ratio_valuation_without_norm_formula hInp hL hTor hBS hBET hNB hBN hTri hTw hBC hRefl hRL
  exact ⟨hDS, hThb, hOne, hBS, hBN, hF, hTor, hDE, hBE, hL, hTri, hTw⟩
end GlobalTheory.SqTop
end

section
theorem _root_.GlobalTheory.T.square_leading_term_bound : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → GlobalTheory.SqTop.Refl → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SqTop.DenSum ∧ GlobalTheory.SqTop.ThbSt ∧ GlobalTheory.SqTop.OneSqSt ∧ GlobalTheory.SqTop.BotSmall ∧ GlobalTheory.SqTop.BotNe ∧ GlobalTheory.SqTop.FieldDat ∧ GlobalTheory.SqTop.TorEx ∧ GlobalTheory.SqTop.DenEx ∧ GlobalTheory.SqTop.BotEx ∧ GlobalTheory.SqTop.LNe ∧ GlobalTheory.SqTop.TriEx ∧ GlobalTheory.SqTop.Tower := by
  first | exact @_root_.GlobalTheory.SqTop.square_top_term_joined_estimates | exact _root_.GlobalTheory.SqTop.square_top_term_joined_estimates | (intros; apply _root_.GlobalTheory.SqTop.square_top_term_joined_estimates <;> assumption)
end
